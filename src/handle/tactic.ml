(** Toplevel commands. *)

open! Lplib
open Common
open Error
open Pos
open Parsing
open Syntax
open Core
open Term
open Proof
open Print
open Timed

(** Logging function for tactics. *)
let log_tact = Logger.make 't' "tact" "tactics"
let log_tact = log_tact.pp

(** Number of admitted axioms in the current signature. Used to name the
    generated axioms. This reference is reset in {!module:Compile} for each
    new compiled module. *)
let admitted : int Stdlib.ref = Stdlib.ref (-1)

(** [add_axiom ss m] adds in signature state [ss] a new axiom symbol of type
   [!(m.meta_type)] and instantiate [m] with it. WARNING: It does not check
   whether the type of [m] contains metavariables. *)
let add_axiom : Sig_state.t -> meta -> Sig_state.t = fun ss m ->
  let name =
    let i = Stdlib.(incr admitted; !admitted) in
    let p = Printf.sprintf "_ax%i" i in
    match m.meta_name with
    | Some n -> Escape.add_suffix (p ^ "_") n
    | _ -> p
  in
  (* Create a symbol with the same type as the metavariable *)
  let ss, sym =
    Console.out 1 (Color.red "axiom %a: %a")
      pp_uid name pp_term !(m.meta_type);
    Sig_state.add_symbol
      ss Public Const Eager true (Pos.none name) !(m.meta_type) [] None
  in
  (* Create the value which will be substituted for the metavariable. This
     value is [sym x0 ... xn] where [xi] are variables that will be
     substituted by the terms of the explicit substitution of the
     metavariable. *)
  let meta_value =
    let vars = Array.init m.meta_arity (new_tvar_ind "x") in
    let ax = _Appl_Symb sym (Array.to_list vars |> List.map _Vari) in
    Bindlib.(bind_mvar vars ax |> unbox)
  in
  LibMeta.set (new_problem()) m meta_value; ss

(** [admit_meta ss m] adds as many axioms as needed in the signature state
   [ss] to instantiate the metavariable [m] by a fresh axiom added to the
   signature [ss]. *)
let admit_meta : Sig_state.t -> meta -> Sig_state.t = fun ss m ->
  let ss = Stdlib.ref ss in
  (* [ms] records the metas that we are instantiating. *)
  let rec admit ms m =
    (* This assertion should be ensured by the typechecking algorithm. *)
    assert (not (MetaSet.mem m ms));
    LibMeta.iter true (admit (MetaSet.add m ms)) [] !(m.meta_type);
    Stdlib.(ss := add_axiom !ss m)
  in
  admit MetaSet.empty m; Stdlib.(!ss)

(** [tac_admit pos ps gt] admits typing goal [gt]. *)
let tac_admit :
      Sig_state.t -> proof_state -> goal_typ -> Sig_state.t * proof_state =
  fun ss ps gt ->
  let ss = admit_meta ss gt.goal_meta in
  ss, remove_solved_goals ps

(** [tac_solve pos ps] tries to simplify the unification goals of the proof
   state [ps] and fails if constraints are unsolvable. *)
let tac_solve : popt -> proof_state -> proof_state = fun pos ps ->
  if Logger.log_enabled () then
    log_tact (Color.red "@[<v>tac_solve@ %a@]") pp_goals ps;
  let gs_typ, gs_unif = List.partition is_typ ps.proof_goals in
  let p = new_problem() in
  let f ms = function
    | Unif _ -> ms
    | Typ gt -> MetaSet.add gt.goal_meta ms
  in
  p := {!p with metas = List.fold_left f MetaSet.empty gs_typ
              ; to_solve = List.rev_map get_constr gs_unif};
  if not (Unif.solve_noexn p) then
    fatal pos "Unification goals are unsatisfiable.";
  (* remove in [gs_typ] the goals that have been instantiated, and simplify
     the others. *)
  let not_instantiated = function
    | Typ gt when !(gt.goal_meta.meta_value) <> None -> None
    | gt -> Some (Goal.simpl Eval.simplify gt)
  in
  let gs_typ = List.filter_map not_instantiated gs_typ in
  {ps with proof_goals = List.map (fun c -> Unif c) !p.unsolved @ gs_typ}

(** [tac_refine pos ps gt gs p t] refines the typing goal [gt] with [t]. [p]
   is the set of metavariables created by the scoping of [t]. *)
let tac_refine :
      popt -> proof_state -> goal_typ -> goal list -> problem -> term
      -> proof_state =
  fun pos ps gt gs p t ->
  if Logger.log_enabled () then
    log_tact (Color.red "@[<v>@[tac_refine@ %a@]@,%a@]%a")
      pp_term t pp_goals ps pp_problem p;
  let c = Env.to_ctxt gt.goal_hyps in
  if LibMeta.occurs gt.goal_meta c t then fatal pos "Circular refinement.";
  (* Check that [t] has the required type. *)
  if not (Infer.check_noexn p c t gt.goal_type) then
    fatal pos "%a@ does not have type@ %a."
      pp_term t
      pp_term gt.goal_type;
  if Logger.log_enabled () then
    log_tact (Color.red "%a ≔ %a") pp_meta gt.goal_meta pp_term t;
  LibMeta.set p gt.goal_meta
    (Bindlib.unbox (Bindlib.bind_mvar (Env.vars gt.goal_hyps) (lift t)));
  (* Convert the metas and constraints of [p] not in [gs] into new goals. *)
  if Logger.log_enabled () then log_tact "%a" pp_problem p;
  tac_solve pos {ps with proof_goals = Proof.add_goals_of_problem p gs}

(** [ind_data t] returns the [ind_data] structure of [s] if [t] is of the
   form [s t1 .. tn] with [s] an inductive type. Fails otherwise. *)
let ind_data : popt -> Env.t -> term -> Sign.ind_data = fun pos env a ->
  let h, ts = get_args (Eval.whnf (Env.to_ctxt env) a) in
  match h with
  | Symb s ->
      let sign = Path.Map.find s.sym_path Sign.(!loaded) in
      begin
        try
          let ind = SymMap.find s !(sign.sign_ind) in
          let ctxt = Env.to_ctxt env in
          if LibTerm.distinct_vars ctxt (Array.of_list ts) = None
          then fatal pos "%a is not applied to distinct variables." pp_sym s
          else ind
        with Not_found -> fatal pos "%a is not an inductive type." pp_sym s
      end
  | _ -> fatal pos "%a is not headed by an inductive type." pp_term a

(** [tac_induction pos ps gt] tries to apply the induction tactic on the
   typing goal [gt]. *)
let tac_induction : popt -> proof_state -> goal_typ -> goal list
    -> proof_state = fun pos ps ({goal_type;goal_hyps;_} as gt) gs ->
  match Eval.whnf (Env.to_ctxt goal_hyps) goal_type with
  | Prod(a,_) ->
      let ind = ind_data pos goal_hyps a in
      let n = ind.ind_nb_params + ind.ind_nb_types + ind.ind_nb_cons in
      let p = new_problem() in
      let t = Env.app_fresh_meta_terms p (mk_Symb ind.ind_prop) n goal_hyps in
      tac_refine pos ps gt gs p t
  | _ -> fatal pos "[%a] is not a product." pp_term goal_type

(** [count_products a] returns the number of consecutive products at
   the top of the term [a]. *)
let count_products : ctxt -> term -> int = fun c ->
  let rec count acc t =
    match Eval.whnf c t with
    | Prod(_,b) -> count (acc + 1) (Bindlib.subst b mk_Kind)
    | _ -> acc
  in count 0

(** [handle ss prv ps tac] applies tactic [tac] in the proof state [ps] and
   returns the new proof state. *)
let handle : Sig_state.t -> bool -> proof_state -> p_tactic -> proof_state =
  fun ss prv ps {elt;pos} ->
  match ps.proof_goals with
  | [] -> assert false (* done before *)
  | g::gs ->
  match elt with
  | P_tac_fail
  | P_tac_query _ -> assert false (* done before *)
  | P_tac_focus(i) ->
      (try {ps with proof_goals = List.swap i ps.proof_goals}
       with Invalid_argument _ -> fatal pos "Invalid goal index.")
  | P_tac_simpl None ->
      {ps with proof_goals = Goal.simpl (Eval.snf []) g :: gs}
  | P_tac_simpl (Some qid) ->
      let s = Sig_state.find_sym ~prt:true ~prv:true ss qid in
      {ps with proof_goals = Goal.simpl (Eval.unfold_sym s) g :: gs}
  | P_tac_solve -> tac_solve pos ps
  | _ ->
  match g with
  | Unif _ -> fatal pos "Not a typing goal."
  | Typ ({goal_hyps=env;_} as gt) ->
  let scope p t = Scope.scope_term prv ss env p
                    (Proof.meta_of_key ps) (Proof.meta_of_name ps) t in
  (* Function for checking that an identifier is not already in use. *)
  let check id =
    if Env.mem id.elt env then fatal id.pos "Identifier already in use." in
  (* Function to apply [n] times the assume tactic. *)
  let assume n =
    if n <= 0 then ps
    else
      let idopt = Some (Pos.none "y") in
      let rec mk_idopts acc k =
        if k <= 0 then acc else mk_idopts (idopt::acc) (k-1) in
      let t = P.abst_list (mk_idopts [] n) P.wild in
      let p = new_problem() in
      tac_refine pos ps gt gs p (scope p t)
  in
  match elt with
  | P_tac_admit
  | P_tac_fail
  | P_tac_focus _
  | P_tac_query _
  | P_tac_simpl _
  | P_tac_solve -> assert false (* done before *)
  | P_tac_apply pt ->
      let p = new_problem() in
      let t = scope p pt in
      (* Compute the product arity of the type of [t]. *)
      (* FIXME: this does not take into account implicit arguments. *)
      let n =
        let c = Env.to_ctxt env in
        match Infer.infer_noexn p c t with
        | None -> fatal pos "[%a] is not typable." pp_term t
        | Some a -> count_products c a
      in
      let p, t = if n <= 0 then p, t
                 else let p = new_problem() in
                      p, scope p (P.appl_wild pt n) in
      tac_refine pos ps gt gs p t
  | P_tac_assume idopts ->
      (* Check that the given identifiers are not already used. *)
      List.iter (Option.iter check) idopts;
      (* Check that the given identifiers are pairwise distinct. *)
      Syntax.check_distinct idopts;
      let p = new_problem() in
      tac_refine pos ps gt gs p (scope p (P.abst_list idopts P.wild))
  | P_tac_generalize {elt=id; pos=idpos} ->
      (* From a goal [e1,id:a,e2 ⊢ ?[e1,id,e2] : u], generate a new goal [e1 ⊢
         ?m[e1] : Π id:a, Π e2, u], and refine [?[e]] with [?m[e1] id e2]. *)
      begin
        try
          let p = new_problem() in
          let e2, x, e1 = List.split (fun (s,_) -> s = id) env in
          let u = lift gt.goal_type in
          let q = Env.to_prod_box [x] (Env.to_prod_box e2 u) in
          let m = LibMeta.fresh p (Env.to_prod e1 q) (List.length e1) in
          let me1 = Bindlib.unbox (_Meta m (Env.to_tbox e1)) in
          let t =
            List.fold_left (fun t (_,(v,_,_)) -> mk_Appl(t, mk_Vari v))
              me1 (x::e2)
          in
          tac_refine pos ps gt gs p t
        with Not_found -> fatal idpos "Unknown hypothesis %a" pp_uid id;
      end
  | P_tac_have(id, t) ->
      (* From a goal [e ⊢ ?[e] : u], generate two new goals [e ⊢ ?1[e] : t]
         and [e,x:t ⊢ ?2[e,x] : u], and refine [?[e]] with [?2[e,?1[e]]. *)
      check id;
      let p = new_problem() in
      let t = scope p t in
      (* Generate the constraints for [t] to be of type [Type]. *)
      let c = Env.to_ctxt gt.goal_hyps in
      if not (Infer.check_noexn p c t mk_Type) then
        fatal pos "%a is not of type Type." pp_term t;
      (* Create a new goal of type [t]. *)
      let n = List.length env in
      let bt = lift t in
      let m1 = LibMeta.fresh p (Env.to_prod env bt) n in
      (* Refine the focused goal. *)
      let v = new_tvar id.elt in
      let env' = Env.add v bt None env in
      let m2 = LibMeta.fresh p (Env.to_prod env' (lift gt.goal_type)) (n+1) in
      let gs = Goal.of_meta m1 :: Goal.of_meta m2 :: gs in
      let ts = Env.to_tbox env in
      let u = Bindlib.unbox (_Meta m2 (Array.append ts [|_Meta m1 ts|])) in
      tac_refine pos ps gt gs p u
  | P_tac_induction -> tac_induction pos ps gt gs
  | P_tac_refine t ->
      let p = new_problem() in tac_refine pos ps gt gs p (scope p t)
  | P_tac_refl ->
      let cfg = Rewrite.get_eq_config ss pos in
      let (a,l,_), vs = Rewrite.get_eq_data cfg pos gt.goal_type in
      let n = Array.length vs in
      (* We first do [n] times the [assume] tactic. *)
      let ps = assume n in
      (* We then apply reflexivity. *)
      begin match ps.proof_goals with
      | Typ gt::gs ->
        let a,l =
          if n = 0 then a,l
          else let (a,l,_),_ = Rewrite.get_eq_data cfg pos gt.goal_type in a,l
        in
        let prf = add_args (mk_Symb cfg.symb_refl) [a; l] in
        let p = new_problem() in tac_refine pos ps gt gs p prf
      | _ -> assert false
      end
  | P_tac_rewrite(l2r,pat,eq) ->
      let pat = Option.map (Scope.scope_rw_patt ss env) pat in
      let p = new_problem() in
      tac_refine pos ps gt gs p
        (Rewrite.rewrite ss p pos gt l2r pat (scope p eq))
  | P_tac_sym ->
      let cfg = Rewrite.get_eq_config ss pos in
      let (a,l,r), vs = Rewrite.get_eq_data cfg pos gt.goal_type in
      let n = Array.length vs in
      (* We first do [n] times the [assume] tactic. *)
      let ps = assume n in
      (* We then apply symmetry. *)
      begin match ps.proof_goals with
      | Typ gt::gs ->
        let a,l,r =
          if n = 0 then a,l,r
          else fst (Rewrite.get_eq_data cfg pos gt.goal_type)
        in
        let p = new_problem() in
        let prf =
          let mt =
            mk_Appl(mk_Symb cfg.symb_P,
                    add_args (mk_Symb cfg.symb_eq) [a; r; l]) in
          let meta_term = LibMeta.make p (Env.to_ctxt gt.goal_hyps) mt in
          (* The proofterm is [eqind a r l M (λx,eq a l x) (refl a l)]. *)
          Rewrite.swap cfg a r l meta_term
        in
        tac_refine pos ps gt gs p prf
      | _ -> assert false
      end
  | P_tac_why3 cfg ->
      let p = new_problem() in
      tac_refine pos ps gt gs p (Why3_tactic.handle ss pos cfg gt)

(** [handle ss prv ps tac] applies tactic [tac] in the proof state [ps] and
   returns the new proof state. *)
let handle : Sig_state.t -> bool -> proof_state -> p_tactic
             -> Sig_state.t * proof_state * Query.result =
  fun ss prv ps ({elt;pos} as tac) ->
  match elt with
  | P_tac_fail -> fatal pos "Call to tactic \"fail\""
  | P_tac_query(q) ->
      if Logger.log_enabled () then log_tact "%a@." Pretty.tactic tac;
      ss, ps, Query.handle ss (Some ps) q
  | _ ->
  match ps.proof_goals with
  | [] -> fatal pos "No remaining goals."
  | Typ gt::_ when elt = P_tac_admit ->
      let ss, ps = tac_admit ss ps gt in ss, ps, None
  | g::_ ->
      if Logger.log_enabled () then
        log_tact "%a@ %a" Proof.Goal.pp g Pretty.tactic tac;
      ss, handle ss prv ps tac, None

let handle : Sig_state.t -> bool -> proof_state -> p_tactic
             -> Sig_state.t * proof_state * Query.result =
  fun ss prv ps tac ->
  try handle ss prv ps tac
  with Fatal _ as e -> Console.out 1 "%a@." pp_goals ps; raise e
