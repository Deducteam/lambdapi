(** Toplevel commands. *)

open! Lplib

open Console
open Terms
open Pos
open Syntax
open Proof
open Print
open Timed

(** Logging function for tactics. *)
let log_tact = new_logger 't' "tact" "tactics"
let log_tact = log_tact.logger

(** [solve_tac ps pos] calls the default solve algorithm on the unification
   goals of the proof state [ps] and fails if constraints are unsolvable. *)
let solve_tac ps pos =
  try
    let gs_typ, gs_unif = List.partition Goal.is_typ ps.proof_goals in
    let to_solve = List.map Goal.get_constr gs_unif in
    let new_cs = Unif.solve {empty_problem with to_solve} in
    let new_gs_unif = List.map Goal.unif new_cs in
    (* remove in [gs_typ] the goals that have been instantiated. *)
    let goal_has_no_meta_value = function
      | Goal.Unif _ -> true
      | Goal.Typ gt ->
          match !(gt.goal_meta.meta_value) with
          | Some _ -> false
          | None -> true
    in
    let gs_typ = List.filter goal_has_no_meta_value gs_typ in
    {ps with proof_goals = new_gs_unif @ gs_typ}
  with Unif.Unsolvable -> fatal pos "Unification goals are unsatisfiable."

(** [handle_tactic ss ps tac] tries to apply the tactic [tac] (in the proof
     state [ps]), and returns the new proof state.  This function fails
     gracefully in case of error. *)
let handle_tactic :
  Sig_state.t -> Terms.expo -> Proof.t -> p_tactic -> Proof.t =
  fun ss e ps tac ->
  match tac.elt with
  | P_tac_query(q) -> Queries.handle_query ss (Some ps) q; ps
  | _ ->
  if ps.proof_goals = [] then fatal tac.pos "There is nothing left to prove.";
  match tac.elt with
  | P_tac_query(_) -> assert false (* Handled above. *)
  | P_tac_solve -> solve_tac ps tac.pos
  | _ ->

  (* Get the unif goals, the first type goal and the following goals *)
  let pre_g, gt, post_g =
    let rec first_goal_typ pre post =
      match post with
      | [] -> assert false
      | Goal.Typ gt :: post -> pre, gt, post
      | (Goal.Unif _ as gu) :: post -> first_goal_typ (pre @ [gu]) post
    in
    first_goal_typ [] ps.proof_goals
  in
  let (env, a), m = Goal.get_type gt, Goal.get_meta gt in
  let scope = Scope.scope_term e ss env in

  let handle_refine : Proof.t -> term -> Proof.t = fun ps t ->
    log_tact "refining [%a] with term [%a]" pp_meta m pp_term t;
    if Basics.occurs m t then fatal tac.pos "Circular refinement.";
    (* Check that [t] is well-typed. *)
    log_tact "proving %a" pp_typing (Env.to_ctxt env, t, a);
    match Infer.check_noexn (Env.to_ctxt env) t a with
    | None -> fatal tac.pos "[%a] cannot have type [%a]." pp_term t pp_term a
    | Some to_solve ->
    let gs_unif = List.map Goal.unif to_solve in
    (* Instantiation. Use Unif.instantiate instead ? *)
    Meta.set m (Bindlib.unbox (Bindlib.bind_mvar (Env.vars env) (lift t)));
    (* New subgoals and focus. *)
    let new_typ_goals = goals_of_metas (Basics.get_metas true t) in
    (* New goals must appear first. *)
    let proof_goals = pre_g @ gs_unif @ new_typ_goals @ post_g in
    let ps = {ps with proof_goals} in
    solve_tac ps tac.pos
  in

  match tac.elt with
  | P_tac_query(_)
  | P_tac_solve -> assert false (* Handled above. *)
  | P_tac_focus(i) ->
      (* Put the [i]-th goal in focus (if possible). *)
      (try {ps with proof_goals = List.swap i ps.proof_goals}
      with Invalid_argument _ -> fatal tac.pos "Invalid goal index.")
  | P_tac_refine(pt) ->
      handle_refine ps (scope pt)
  | P_tac_intro(idopts) ->
      handle_refine ps (scope (P.abst_list idopts P.wild))
  | P_tac_apply(pt) ->
      let t = scope pt in
      (* Compute the product arity of the type of [t]. *)
      let n =
        match Infer.infer_noexn (Env.to_ctxt env) t with
        | None -> fatal tac.pos "[%a] is not typable." pp_term t
        | Some (a, to_solve) -> Basics.count_products a
      in
      (*FIXME: this does not take into account implicit arguments. *)
      let t = if n <= 0 then t else scope (P.appl_wild pt n) in
      handle_refine ps t
  | P_tac_simpl ->
      let new_goal_typ = Goal.Typ (Goal.simpl gt) in
      let proof_goals = pre_g @ new_goal_typ :: post_g in
      {ps with proof_goals}
  | P_tac_rewrite(b,po,pt) ->
      let po = Option.map (Scope.scope_rw_patt ss env) po in
      handle_refine ps (Rewrite.rewrite ss tac.pos ps b po (scope pt))
  | P_tac_refl ->
      handle_refine ps (Rewrite.reflexivity ss tac.pos ps)
  | P_tac_sym ->
      handle_refine ps (Rewrite.symmetry ss tac.pos ps)
  | P_tac_why3(config) ->
      handle_refine ps (Why3_tactic.handle ss tac.pos config gt)
  | P_tac_fail -> fatal tac.pos "Call to tactic \"fail\""

let handle_tactic :
  Sig_state.t -> Terms.expo -> Proof.t -> p_tactic -> Proof.t =
  fun ss exp ps tac ->
  try handle_tactic ss exp ps tac
  with Fatal(_,_) as e -> out 1 "%a" Proof.pp_goals ps; raise e
