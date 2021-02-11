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
let tac_refine : popt -> proof_state -> term -> proof_state =
  fun pos ps t ->
  match ps.proof_goals with
  | [] -> fatal pos "No remaining goals."
  | Unif _::_ -> fatal pos "Not a typing goal."
  | Typ gt::gs ->
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
            (Bindlib.unbox (Bindlib.bind_mvar (Env.vars gt.goal_hyps)
                              (lift t)));
          (* Convert the metas of [t] not in [gs] into new goals. *)
          let gs_typ = add_goals_of_metas (LibTerm.get_metas true t) gs_typ in
          let proof_goals = List.rev_map (fun c -> Unif c) cs @ gs_typ in
          tac_solve pos {ps with proof_goals}

(** [handle ss e ps tac] applies tactic [tac] in the proof state
   [ps] and returns the new proof state. This function fails gracefully in
   case of error. *)
let handle :
  Sig_state.t -> Tags.expo -> proof_state -> p_tactic ->
    proof_state * Query.result =
  fun ss e ps tac ->
  if !log_enabled then
    begin
      (match ps.proof_goals with
       | g::_ -> log_tact "%a" Proof.Goal.pp g
       | [] -> ());
      log_tact "%a" Pretty.tactic tac
    end;
  match tac.elt with
  | P_tac_query(q) -> ps, Query.handle ss (Some ps) q
  | P_tac_solve -> tac_solve tac.pos ps, None
  | P_tac_focus(i) ->
      (try {ps with proof_goals = List.swap i ps.proof_goals}, None
      with Invalid_argument _ -> fatal tac.pos "Invalid goal index.")
  | P_tac_refine(pt) ->
      let env = Proof.focus_env (Some ps) in
      tac_refine tac.pos ps (Scope.scope_term e ss env pt), None
  | P_tac_intro(idopts) ->
      let env = Proof.focus_env (Some ps) in
      let t = Scope.scope_term e ss env (P.abst_list idopts P.wild) in
      tac_refine tac.pos ps t, None
  | P_tac_apply(pt) ->
      let env = Proof.focus_env (Some ps) in
      let t = Scope.scope_term e ss env pt in
      (* Compute the product arity of the type of [t]. *)
      let n =
        match Infer.infer_noexn [] (Env.to_ctxt env) t with
        | None -> fatal tac.pos "[%a] is not typable." pp_term t
        | Some (a, _) -> LibTerm.count_products a
      in
      (*FIXME: this does not take into account implicit arguments. *)
      let t = if n <= 0 then t
              else Scope.scope_term e ss env (P.appl_wild pt n) in
      tac_refine tac.pos ps t, None
  | P_tac_simpl ->
      (match ps.proof_goals with
       | [] -> fatal tac.pos "No remaining goals."
       | g::gs -> {ps with proof_goals = Goal.simpl g :: gs}), None
  | P_tac_rewrite(b,po,pt) ->
      let env = Proof.focus_env (Some ps) in
      let po = Option.map (Scope.scope_rw_patt ss env) po in
      let t = Scope.scope_term e ss env pt in
      tac_refine tac.pos ps (Rewrite.rewrite ss tac.pos ps b po t), None
  | P_tac_refl ->
      tac_refine tac.pos ps (Rewrite.reflexivity ss tac.pos ps), None
  | P_tac_sym ->
      tac_refine tac.pos ps (Rewrite.symmetry ss tac.pos ps), None
  | P_tac_why3(config) ->
      (match ps.proof_goals with
       | [] -> fatal tac.pos "No remaining goals."
       | Unif _::_ -> fatal tac.pos "Not a typing goal."
       | Typ gt::_ ->
          (tac_refine tac.pos ps (Why3_tactic.handle ss tac.pos config gt)),
            None)
  | P_tac_fail -> fatal tac.pos "Call to tactic \"fail\""

let handle :
  Sig_state.t -> Tags.expo -> proof_state -> p_tactic ->
    proof_state * Query.result =
  fun ss exp ps tac ->
  try handle ss exp ps tac
  with Fatal(_,_) as e -> Console.out 1 "%a" Proof.pp_goals ps; raise e
