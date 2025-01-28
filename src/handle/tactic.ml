(** Handling of tactics. *)

open Lplib
open Common open Error open Pos
open Parsing open Syntax
open Core open Term open Print
open Proof
open Timed

(** Logging function for tactics. *)
let log = Logger.make 't' "tact" "tactics"
let log = log.pp

(** Number of admitted axioms in the current signature. Used to name the
    generated axioms. This reference is reset in {!module:Compile} for each
    new compiled module. *)
let admitted_initial_value = min_int
let admitted : int Stdlib.ref = Stdlib.ref admitted_initial_value
let reset_admitted() = Stdlib.(admitted := admitted_initial_value)

(** [add_axiom ss sym_pos m] adds in signature state [ss] a new axiom symbol
    of type [!(m.meta_type)] and instantiate [m] with it. WARNING: It does not
    check whether the type of [m] contains metavariables. Return updated
    signature state [ss] and the new axiom symbol.*)
let add_axiom : Sig_state.t -> popt -> meta -> sym =
  fun ss sym_pos m ->
  let name =
    let i = Stdlib.(incr admitted; !admitted) in
    assert (i<=0);
    Printf.sprintf "_ax%i" (i + max_int)
  in
  (* Create a symbol with the same type as the metavariable *)
  let sym =
    Console.out 1 (Color.red "axiom %a: %a") uid name term !(m.meta_type);
    (* Temporary hack for axioms to have a declaration position in the order
       they are created. *)
    let pos = shift Stdlib.(!admitted) sym_pos in
    let id = Pos.make pos name in
    (* We ignore the new ss returned by Sig_state.add_symbol: axioms do not
       need to be in scope. *)
    snd (Sig_state.add_symbol ss
           Public Defin Eager true id None !(m.meta_type) [] None)
  in
  (* Create the value which will be substituted for the metavariable. This
     value is [sym x0 ... xn] where [xi] are variables that will be
     substituted by the terms of the explicit substitution of the
     metavariable. *)
  let meta_value =
    let vars = Array.init m.meta_arity (new_var_ind "x") in
    let ax = add_args (mk_Symb sym) (List.map mk_Vari (Array.to_list vars)) in
    bind_mvar vars ax
  in
  LibMeta.set (new_problem()) m meta_value; sym

(** [admit_meta ss sym_pos m] adds as many axioms as needed in the signature
   state [ss] to instantiate the metavariable [m] by a fresh axiom added to
   the signature [ss]. *)
let admit_meta : Sig_state.t -> popt -> meta -> unit =
  fun ss sym_pos m ->
  (* [ms] records the metas that we are instantiating. *)
  let rec admit ms m =
    (* This assertion should be ensured by the typechecking algorithm. *)
    assert (not (MetaSet.mem m ms));
    LibMeta.iter true (admit (MetaSet.add m ms)) [] !(m.meta_type);
    ignore (add_axiom ss sym_pos m)
  in
  admit MetaSet.empty m

(** [tac_admit ss pos ps gt] admits typing goal [gt]. *)
let tac_admit: Sig_state.t -> popt -> proof_state -> goal_typ -> proof_state =
  fun ss sym_pos ps gt ->
  admit_meta ss sym_pos gt.goal_meta; remove_solved_goals ps

(** [tac_solve pos ps] tries to simplify the unification goals of the proof
   state [ps] and fails if constraints are unsolvable. *)
let tac_solve : popt -> proof_state -> proof_state = fun pos ps ->
  if Logger.log_enabled () then log "@[<v>tac_solve@ %a@]" goals ps;
  (* convert the proof_state into a problem *)
  let gs_typ, gs_unif = List.partition is_typ ps.proof_goals in
  let p = new_problem() in
  let add_meta ms = function
    | Unif _ -> ms
    | Typ gt -> MetaSet.add gt.goal_meta ms
  in
  p := {!p with metas = List.fold_left add_meta MetaSet.empty gs_typ
              ; to_solve = List.rev_map get_constr gs_unif};
  (* try to solve the problem *)
  if not (Unif.solve_noexn p) then
    fatal pos "Unification goals are unsatisfiable.";
  (* compute the new list of goals by preserving the order of initial goals
     and adding the new goals at the end *)
  let non_instantiated g =
    match g with
    | Typ gt when !(gt.goal_meta.meta_value) = None ->
        Some (Goal.simpl Eval.simplify g)
    | _ -> None
  in
  let gs_typ = List.filter_map non_instantiated gs_typ in
  let is_eq_goal_meta m = function
    | Typ gt -> m == gt.goal_meta
    | _ -> assert false
  in
  let add_goal m gs =
    if List.exists (is_eq_goal_meta m) gs_typ then gs
    else Goal.of_meta m :: gs
  in
  let proof_goals =
    gs_typ @ MetaSet.fold add_goal (!p).metas
               (List.map (fun c -> Unif c) (!p).unsolved)
  in
  {ps with proof_goals}

(** [tac_refine pos ps gt gs p t] refines the typing goal [gt] with [t]. [p]
   is the set of metavariables created by the scoping of [t]. *)
let tac_refine : ?check:bool ->
      popt -> proof_state -> goal_typ -> goal list -> problem -> term
      -> proof_state =
  fun ?(check=true) pos ps gt gs p t ->
  if Logger.log_enabled () then log "@[tac_refine@ %a@]" term t;
  let c = Env.to_ctxt gt.goal_hyps in
  if LibMeta.occurs gt.goal_meta c t then fatal pos "Circular refinement.";
  (* Check that [t] has the required type. *)
  let t =
    if check then
      match Infer.check_noexn p c t gt.goal_type with
      | None ->
        fatal pos "%a@ does not have type@ %a." term t term gt.goal_type
      | Some t -> t
    else t
  in
  if Logger.log_enabled () then
    log (Color.red "%a ≔ %a") meta gt.goal_meta term t;
  LibMeta.set p gt.goal_meta (bind_mvar (Env.vars gt.goal_hyps) t);
  (* Convert the metas and constraints of [p] not in [gs] into new goals. *)
  if Logger.log_enabled () then log "%a" problem p;
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
          let _, ts = List.cut ts ind.ind_nb_params (*remove parameters*) in
          let ctxt = Env.to_ctxt env in
          if LibTerm.distinct_vars ctxt (Array.of_list ts) = None
          then fatal pos "%a is not applied to distinct variables." sym s
          else ind
        with Not_found -> fatal pos "%a is not an inductive type." sym s
      end
  | _ -> fatal pos "%a is not headed by an inductive type." term a

(** [tac_induction pos ps gt] tries to apply the induction tactic on the
   typing goal [gt]. *)
let tac_induction : popt -> proof_state -> goal_typ -> goal list
    -> proof_state = fun pos ps ({goal_type;goal_hyps;_} as gt) gs ->
  let ctx = Env.to_ctxt goal_hyps in
  match Eval.whnf ctx goal_type with
  | Prod(a,_) ->
      let ind = ind_data pos goal_hyps a in
      let n = ind.ind_nb_params + ind.ind_nb_types + ind.ind_nb_cons in
      let p = new_problem () in
      let metas =
        let fresh_meta _ =
          let mt = LibMeta.make p ctx mk_Type in
          LibMeta.make p ctx mt
        in
        (* Reverse to have goals properly sorted. *)
        List.(rev (init (n - 1) fresh_meta))
      in
      let t = add_args (mk_Symb ind.ind_prop) metas in
      tac_refine pos ps gt gs p t
  | _ -> fatal pos "[%a] is not a product." term goal_type

(** [count_products a] returns the number of consecutive products at
   the top of the term [a]. *)
let count_products : ctxt -> term -> int = fun c ->
  let rec count acc t =
    match Eval.whnf c t with
    | Prod(_,b) -> count (acc + 1) (subst b mk_Kind)
    | _ -> acc
  in count 0

(** [get_prod_ids env do_whnf t] returns the list [v1;..;vn] if [do_whnf] is
    true and [whnf t] is of the form [Π v1:A1, .., Π vn:An, u] with [u] not a
    product, or if [do_whnf] is false and [t] is of the form [Π v1:A1, .., Π
    vn:An, u] with [u] not a product. *)
let get_prod_ids env =
  let rec aux acc do_whnf t =
    match get_args t with
    | Prod(_,b), _ ->
        let x,b = unbind b in
        aux (base_name x::acc) do_whnf b
    | _ ->
        if do_whnf then aux acc false (Eval.whnf (Env.to_ctxt env) t)
        else List.rev acc
  in aux []

(** [gen_valid_idopts env ids] generates a list of pairwise distinct
    identifiers distinct from those of [env] to replace [ids]. *)
let gen_valid_idopts env ids =
  let add_decl ids (s,_) = Extra.StrSet.add s ids in
  let idset = ref (List.fold_left add_decl Extra.StrSet.empty env) in
  let f id idopts =
    let id = Extra.get_safe_prefix id !idset in
    idset := Extra.StrSet.add id !idset;
    Some(Pos.none id)::idopts
  in
  List.fold_right f ids []

(** [handle ss sym_pos prv ps tac] applies tactic [tac] in the proof state
   [ps] and returns the new proof state. *)
let rec handle :
  Sig_state.t -> popt -> bool -> proof_state -> p_tactic -> proof_state =
  fun ss sym_pos prv ps {elt;pos} ->
  match ps.proof_goals with
  | [] -> assert false (* done before *)
  | g::gs ->
  match elt with
  | P_tac_fail
  | P_tac_query _ -> assert false (* done before *)
  (* Tactics that apply to both unification and typing goals: *)
  | P_tac_simpl None ->
      {ps with proof_goals = Goal.simpl Eval.snf g :: gs}
  | P_tac_simpl (Some qid) ->
      let s = Sig_state.find_sym ~prt:true ~prv:true ss qid in
      {ps with proof_goals = Goal.simpl (fun _ -> Eval.unfold_sym s) g :: gs}
  | P_tac_solve -> tac_solve pos ps
  | _ ->
  (* Tactics that apply to typing goals only: *)
  match g with
  | Unif _ -> fatal pos "Not a typing goal."
  | Typ ({goal_hyps=env;_} as gt) ->
  let scope t = Scope.scope_term ~mok:(Proof.meta_of_key ps) prv ss env t in
  (* Function to apply the assume tactic several times without checking the
     validity of identifiers. *)
  let assume idopts =
    match idopts with
    | [] -> ps
    | _ -> tac_refine pos ps gt gs (new_problem())
             (scope (P.abst_list idopts P.wild))
  in
  (* Function for checking that an identifier is not already in use. *)
  let check id =
    if Env.mem id.elt env then fatal id.pos "Identifier already in use." in
  match elt with
  | P_tac_fail
  | P_tac_query _
  | P_tac_simpl _
  | P_tac_solve -> assert false (* done before *)
  | P_tac_admit -> tac_admit ss sym_pos ps gt
  | P_tac_apply pt ->
      let t = scope pt in
      (* Compute the product arity of the type of [t]. *)
      (* FIXME: this does not take into account implicit arguments. *)
      let n =
        let c = Env.to_ctxt env in
        let p = new_problem () in
        match Infer.infer_noexn p c t with
        | None -> fatal pos "[%a] is not typable." term t
        | Some (_, a) -> count_products c a
      in
      let t = scope (P.appl_wild pt n) in
      let p = new_problem () in
      tac_refine pos ps gt gs p t
  | P_tac_assume idopts ->
      (* Check that no idopt is None. *)
      if List.exists ((=) None) idopts then
        fatal pos "underscores not allowed in assume";
      (* Check that the given identifiers are not already used. *)
      List.iter (Option.iter check) idopts;
      (* Check that the given identifiers are pairwise distinct. *)
      Syntax.check_distinct_idopts idopts;
      assume idopts
  | P_tac_generalize {elt=id; pos=idpos} ->
      (* From a goal [e1,id:a,e2 ⊢ ?[e1,id,e2] : u], generate a new goal [e1 ⊢
         ?m[e1] : Π id:a, Π e2, u], and refine [?[e]] with [?m[e1] id e2]. *)
      begin
        try
          let p = new_problem() in
          let e2, x, e1 = List.split (fun (s,_) -> s = id) env in
          let u = gt.goal_type in
          let q = Env.to_prod [x] (Env.to_prod e2 u) in
          let m = LibMeta.fresh p (Env.to_prod e1 q) (List.length e1) in
          let me1 = mk_Meta (m, Env.to_terms e1) in
          let t =
            List.fold_left (fun t (_,(v,_,_)) -> mk_Appl(t, mk_Vari v))
              me1 (x :: List.rev e2)
          in
          tac_refine pos ps gt gs p t
        with Not_found -> fatal idpos "Unknown hypothesis %a" uid id;
      end
  | P_tac_have(id, t) ->
      (* From a goal [e ⊢ ?[e] : u], generate two new goals [e ⊢ ?1[e] : t]
         and [e,x:t ⊢ ?2[e,x] : u], and refine [?[e]] with [?2[e,?1[e]]. *)
      check id;
      let p = new_problem() in
      let t = scope t in
      (* Generate the constraints for [t] to be of type [Type]. *)
      let c = Env.to_ctxt env in
      begin
        match Infer.check_noexn p c t mk_Type with
        | None -> fatal pos "%a is not of type Type." term t
        | Some t ->
        (* Create a new goal of type [t]. *)
        let n = List.length env in
        let m1 = LibMeta.fresh p (Env.to_prod env t) n in
        (* Refine the focused goal. *)
        let v = new_var id.elt in
        let env' = Env.add id.elt v t None env in
        let m2 = LibMeta.fresh p (Env.to_prod env' gt.goal_type) (n+1) in
        let ts = Env.to_terms env in
        let u = mk_Meta (m2, Array.append ts [|mk_Meta (m1, ts)|]) in
        tac_refine pos ps gt gs p u
      end
  | P_tac_set(id,t) ->
      (* From a goal [e ⊢ ?[e]:a], generate a new goal [e,id:b ⊢ ?1[e,x]:a],
         where [b] is the type of [t], and refine [?[e]] with [?1[e,t]]. *)
      check id;
      let p = new_problem() in
      let t = scope t in
      let c = Env.to_ctxt env in
      begin
        match Infer.infer_noexn p c t with
        | None -> fatal pos "%a is not typable." term t
        | Some (t,b) ->
          let x = new_var id.elt in
          let e' = Env.add id.elt x b (Some t) env in
          let a = gt.goal_type in
          let m = LibMeta.fresh p (Env.to_prod e' a) (List.length e') in
          let u = mk_Meta(m, Array.append (Env.to_terms env) [|t|]) in
          (*tac_refine pos ps gt gs p (Bindlib.unbox u)*)
          LibMeta.set p gt.goal_meta (bind_mvar (Env.vars env) u);
          (*let g = Goal.of_meta m in*)
          let g = Typ {goal_meta=m; goal_hyps=e'; goal_type=gt.goal_type} in
          {ps with proof_goals = g :: gs}
      end
  | P_tac_induction -> tac_induction pos ps gt gs
  | P_tac_refine t -> tac_refine pos ps gt gs (new_problem()) (scope t)
  | P_tac_refl ->
      begin
        let cfg = Rewrite.get_eq_config ss pos in
        let _,vs = Rewrite.get_eq_data cfg pos gt.goal_type in
        let idopts = gen_valid_idopts env (List.map base_name vs) in
        let ps = assume idopts in
        match ps.proof_goals with
        | [] -> assert false
        | Unif _::_ -> assert false
        | Typ gt::gs ->
            let cfg = Rewrite.get_eq_config ss pos in
            let (a,l,_),_ = Rewrite.get_eq_data cfg pos gt.goal_type in
            let prf = add_args (mk_Symb cfg.symb_refl) [a; l] in
            tac_refine pos ps gt gs (new_problem()) prf
      end
  | P_tac_remove ids ->
      (* Remove hypothesis [id] in goal [g]. *)
      let remove g id =
        match g with
        | Unif _ -> assert false
        | Typ gt ->
            let k =
              try List.pos (fun (s,_) -> s = id.elt) env
              with Not_found -> fatal id.pos "Unknown hypothesis."
            in
            let m = gt.goal_meta in
            let n = m.meta_arity - 1 in
            let a = cleanup !(m.meta_type) in (* cleanup necessary *)
            let b = LibTerm.codom_binder (n - k) a in
            if binder_occur b then
              fatal id.pos "%s cannot be removed because of dependencies."
                id.elt;
            let env' = List.filter (fun (s,_) -> s <> id.elt) env in
            let a' = Env.to_prod env' gt.goal_type in
            let p = new_problem() in
            let m' = LibMeta.fresh p a' n in
            let t = mk_Meta(m',Env.to_terms env') in
            LibMeta.set p m (bind_mvar (Env.vars env) t);
            Goal.of_meta m'
      in
      Syntax.check_distinct ids;
      (* Reorder [ids] wrt their positions. *)
      let n = gt.goal_meta.meta_arity - 1 in
      let id_pos id =
        try id, n - List.pos (fun (s,_) -> s = id.elt) env
        with Not_found -> fatal id.pos "Unknown hypothesis."
      in
      let cmp (_,k1) (_,k2) = Stdlib.compare k2 k1 in
      let ids = List.map fst (List.sort cmp (List.map id_pos ids)) in
      let g = List.fold_left remove g ids in
      {ps with proof_goals = g::gs}
  | P_tac_rewrite(l2r,pat,eq) ->
      let pat = Option.map (Scope.scope_rw_patt ss env) pat in
      let p = new_problem() in
      tac_refine pos ps gt gs p
        (Rewrite.rewrite ss p pos gt l2r pat (scope eq))
  | P_tac_sym ->
      let cfg = Rewrite.get_eq_config ss pos in
      let (a,l,r),_ = Rewrite.get_eq_data cfg pos gt.goal_type in
      let p = new_problem() in
      let prf =
        let mt = mk_Appl(mk_Symb cfg.symb_P,
                         add_args (mk_Symb cfg.symb_eq) [a;r;l]) in
        let meta_term = LibMeta.make p (Env.to_ctxt env) mt in
        (* The proofterm is [eqind a r l M (λx,eq a l x) (refl a l)]. *)
        Rewrite.swap cfg a r l meta_term
      in
      tac_refine pos ps gt gs p prf
  | P_tac_why3 cfg ->
      begin
        let ids = get_prod_ids env false gt.goal_type in
        let idopts = gen_valid_idopts env ids in
        let ps = assume idopts in
        match ps.proof_goals with
        | Typ gt::_ ->
            Why3_tactic.handle ss pos cfg gt; tac_admit ss sym_pos ps gt
        | _ -> assert false
      end
  | P_tac_try tactic ->
    try handle ss sym_pos prv ps tactic
    with Fatal(_, _s) -> ps

(** Representation of a tactic output. *)
type tac_output = proof_state * Query.result

(** [handle ss sym_pos prv ps tac] applies tactic [tac] in the proof state
   [ps] and returns the new proof state. *)
let handle :
  Sig_state.t -> popt -> bool -> proof_state -> p_tactic -> tac_output =
  fun ss sym_pos prv ps ({elt;pos} as tac) ->
  match elt with
  | P_tac_fail -> fatal pos "Call to tactic \"fail\""
  | P_tac_query(q) ->
    if Logger.log_enabled () then log "%a@." Pretty.tactic tac;
    ps, Query.handle ss (Some ps) q
  | _ ->
  match ps.proof_goals with
  | [] -> fatal pos "No remaining goals."
  | g::_ ->
    if Logger.log_enabled () then
      log ("%a@\n" ^^ Color.red "%a") Proof.Goal.pp g Pretty.tactic tac;
    handle ss sym_pos prv ps tac, None

(** [handle sym_pos prv r tac n] applies the tactic [tac] from the previous
   tactic output [r] and checks that the number of goals of the new proof
   state is compatible with the number [n] of subproofs. *)
let handle :
  Sig_state.t -> popt -> bool -> tac_output -> p_tactic -> int -> tac_output =
  fun ss sym_pos prv (ps, _) t nb_subproofs ->
  let (ps', _) as a = handle ss sym_pos prv ps t in
  let nb_goals_before = List.length ps.proof_goals in
  let nb_goals_after = List.length ps'.proof_goals in
  let nb_newgoals = nb_goals_after - nb_goals_before in
  if nb_newgoals <= 0 then
    if nb_subproofs = 0 then a
    else fatal t.pos "A subproof is given but there is no subgoal."
  else if is_destructive t then
    match nb_newgoals + 1 - nb_subproofs with
    | 0 -> a
    | n when n > 0 ->
      fatal t.pos "Missing subproofs (%d subproofs for %d subgoals):@.%a"
        nb_subproofs (nb_newgoals + 1) goals ps'
    | _ ->
      fatal t.pos "Too many subproofs (%d subproofs for %d subgoals):@.%a"
        nb_subproofs (nb_newgoals + 1) goals ps'
  else match nb_newgoals - nb_subproofs with
    | 0 -> a
    | n when n > 0 ->
      fatal t.pos "Missing subproofs (%d subproofs for %d subgoals):@.%a"
        nb_subproofs nb_newgoals goals ps'
    | _ -> fatal t.pos "Too many subproofs (%d subproofs for %d subgoals)."
             nb_subproofs nb_newgoals
