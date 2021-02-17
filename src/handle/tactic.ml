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
open Debug

(** Logging function for tactics. *)
let log_tact = new_logger 't' "tact" "tactics"
let log_tact = log_tact.logger

(** [tac_solve pos ps] tries to simplify the unification goals of the proof
   state [ps] and fails if constraints are unsolvable. *)
let tac_solve : popt -> proof_state -> proof_state = fun pos ps ->
  if !log_enabled then log_tact "solve";
  try
    let gs_typ, gs_unif = List.partition is_typ ps.proof_goals in
    let to_solve = List.map get_constr gs_unif in
    let new_cs = Unif.solve {empty_problem with to_solve} in
    let new_gs_unif = List.map (fun c -> Unif c) new_cs in
    (* remove in [gs_typ] the goals that have been instantiated. *)
    let goal_has_no_meta_value = function
      | Unif _ -> true
      | Typ gt ->
          match !(gt.goal_meta.meta_value) with
          | Some _ -> false
          | None -> true
    in
    let gs_typ = List.filter goal_has_no_meta_value gs_typ in
    {ps with proof_goals = new_gs_unif @ gs_typ}
  with Unif.Unsolvable -> fatal pos "Unification goals are unsatisfiable."

(** [tac_refine pos ps t] refines the focused typing goal with [t]. *)
let tac_refine : popt -> proof_state -> goal_typ -> goal list -> term
                 -> proof_state = fun pos ps gt gs t ->
  if !log_enabled then
    log_tact "refine %a with %a" pp_meta gt.goal_meta pp_term t;
  if LibTerm.occurs gt.goal_meta t then fatal pos "Circular refinement.";
  (* Check that [t] is well-typed. *)
  let gs_typ, gs_unif = List.partition is_typ gs in
  let to_solve = List.map get_constr gs_unif in
  let c = Env.to_ctxt gt.goal_hyps in
  match Infer.check_noexn to_solve c t gt.goal_type with
  | None -> fatal pos "[%a] cannot have type [%a]."
              pp_term t pp_term gt.goal_type
  | Some cs ->
      (* Instantiation. Use Unif.instantiate instead ? *)
      Meta.set gt.goal_meta
        (Bindlib.unbox (Bindlib.bind_mvar (Env.vars gt.goal_hyps) (lift t)));
      (* Convert the metas of [t] not in [gs] into new goals. *)
      let gs_typ = add_goals_of_metas (LibTerm.get_metas true t) gs_typ in
      let proof_goals = List.rev_map (fun c -> Unif c) cs @ gs_typ in
      tac_solve pos {ps with proof_goals}

(** [induction t] returns the [inductive] structure of [s] if [t] is of the
   form [s t1 .. tn] with [s] an inductive type. Fails otherwise. *)
let inductive : popt -> Env.t -> term -> Sign.inductive = fun pos env a ->
  let h, ts = LibTerm.get_args a in
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

(** [tac_induction pos ps gt] tries to apply the induction tactic on the goal
   type [gt]. *)
let tac_induction : popt -> proof_state -> goal_typ -> goal list
    -> proof_state = fun pos ps ({goal_type;goal_hyps;_} as gt) gs ->
  match unfold goal_type with
  | Prod(a,_) ->
      let ind = inductive pos goal_hyps a in
      let n = ind.ind_nb_params + ind.ind_nb_types + ind.ind_nb_cons in
      let t = Env.add_fresh_metas goal_hyps (Symb ind.ind_prop) n in
      tac_refine pos ps gt gs t
  | _ -> fatal pos "[%a] is not a product." pp_term goal_type

(** [handle ss expo ps tac] applies tactic [tac] in the proof state [ps] and
   returns the new proof state. *)
let handle : Sig_state.t -> Tags.expo -> proof_state -> p_tactic
             -> proof_state = fun ss expo ps {elt;pos} ->
  match ps.proof_goals with
  | [] -> assert false (* done before *)
  | g::gs ->
  match elt with
  | P_tac_fail
  | P_tac_query _ -> assert false (* done before *)
  | P_tac_focus(i) ->
      (try {ps with proof_goals = List.swap i ps.proof_goals}
       with Invalid_argument _ -> fatal pos "Invalid goal index.")
  | P_tac_simpl -> {ps with proof_goals = Goal.simpl g :: gs}
  | P_tac_solve -> tac_solve pos ps
  | _ ->
  match g with
  | Unif _ -> fatal pos "Not a typing goal."
  | Typ ({goal_hyps=env;_} as gt) ->
  match elt with
  | P_tac_fail
  | P_tac_focus _
  | P_tac_query _
  | P_tac_simpl
  | P_tac_solve -> assert false (* done before *)
  | P_tac_apply(pt) ->
      let t = Scope.scope_term expo ss env pt in
      (* Compute the product arity of the type of [t]. *)
      (*FIXME: this does not take into account implicit arguments. *)
      let n =
        match Infer.infer_noexn [] (Env.to_ctxt env) t with
        | None -> fatal pos "[%a] is not typable." pp_term t
        | Some (a, _) -> LibTerm.count_products a
      in
      let t = if n <= 0 then t
              else Scope.scope_term expo ss env (P.appl_wild pt n) in
      tac_refine pos ps gt gs t
  | P_tac_assume(idopts) ->
      let t = Scope.scope_term expo ss env (P.abst_list idopts P.wild) in
      tac_refine pos ps gt gs t
  | P_tac_induction -> tac_induction pos ps gt gs
  | P_tac_refine t ->
      tac_refine pos ps gt gs (Scope.scope_term expo ss env t)
  | P_tac_refl -> tac_refine pos ps gt gs (Rewrite.reflexivity ss pos gt)
  | P_tac_rewrite(l2r,pat,eq) ->
      let pat = Option.map (Scope.scope_rw_patt ss env) pat in
      let eq = Scope.scope_term expo ss env eq in
      tac_refine pos ps gt gs (Rewrite.rewrite ss pos gt l2r pat eq)
  | P_tac_sym -> tac_refine pos ps gt gs (Rewrite.symmetry ss pos gt)
  | P_tac_why3(config) ->
      tac_refine pos ps gt gs (Why3_tactic.handle ss pos config gt)

(** [handle ss expo ps tac] applies tactic [tac] in the proof state [ps] and
   returns the new proof state. *)
let handle : Sig_state.t -> Tags.expo -> proof_state -> p_tactic
             -> proof_state * Query.result =
  fun ss expo ps ({elt;pos} as tac) ->
  match elt with
  | P_tac_fail -> fatal pos "Call to tactic \"fail\""
  | P_tac_query(q) ->
      if !log_enabled then log_tact "%a" Pretty.tactic tac;
      ps, Query.handle ss (Some ps) q
  | _ ->
  match ps.proof_goals with
  | [] -> fatal pos "No remaining goals."
  | g::_ ->
      if !log_enabled then log_tact "%a%a" Proof.Goal.pp g Pretty.tactic tac;
      handle ss expo ps tac, None

let handle : Sig_state.t -> Tags.expo -> proof_state -> p_tactic
             -> proof_state * Query.result = fun ss expo ps tac ->
  try handle ss expo ps tac
  with Fatal(_,_) as e -> Console.out 1 "%a" Proof.pp_goals ps; raise e
