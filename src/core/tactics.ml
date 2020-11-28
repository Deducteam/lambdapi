(** Toplevel commands. *)

open! Lplib

open Console
open Terms
open Pos
open Syntax
open Proof
open Print
open P_terms

type nonrec ast         = (p_term, p_rule) ast
type nonrec p_command   = (p_term, p_rule) p_command
type nonrec p_arg       = p_term Syntax.p_arg
type nonrec p_rule      = p_rule
type nonrec p_rw_patt   = p_term p_rw_patt
type nonrec p_tactic    = p_term p_tactic
type nonrec p_assertion = p_term p_assertion
type nonrec p_query     = p_term p_query

(** Logging function for tactics. *)
let log_tact = new_logger 't' "tact" "tactics"
let log_tact = log_tact.logger

(** [handle_tactic ss ps tac] tries to apply the tactic [tac] (in the proof
     state [ps]), and returns the new proof state.  This function fails
     gracefully in case of error. *)
let handle_tactic : Sig_state.t -> Proof.t -> p_tactic -> Proof.t =
  fun ss ps tac ->
  (* First handle the tactics that do not change the goals. *)
  match tac.elt with
  | P_tac_print         ->
      (* Just print the current proof state. *)
      Console.out 1 "%a" pp_goals ps; ps
  | P_tac_proofterm     ->
      (* Just print the current proof term. *)
      let t = Meta(ps.proof_term, [||]) in
      let name = ps.proof_name.elt in
      Console.out 1 "Proof term for %s: %a\n" name pp_term t; ps
  | P_tac_query(q)      ->
      Queries.handle_query ss (Some ps) q; ps
  | _                   ->
  (* The other tactics may change the goals. *)
  (* Get the focused goal and the other goals. *)
  let (g, gs) =
    match ps.proof_goals with
    | []    -> fatal tac.pos "There is nothing left to prove.";
    | g::gs -> (g, gs)
  in
  (* Obtaining the goal environment and type. *)
  let (env, a) = Goal.get_type g in

  let scope = Scope.scope_term Public ss env in
  let infer t = Typing.infer (Env.to_ctxt env) t in
  let check t a = Typing.check (Env.to_ctxt env) t a in

  let handle_refine : term -> Proof.t = fun t ->
    (* Check if the goal metavariable appears in [t]. *)
    let m = Goal.get_meta g in
    log_tact "refining [%a] with term [%a]" pp_meta m pp_term t;
    if Basics.occurs m t then fatal tac.pos "Circular refinement.";
    (* Check that [t] is well-typed. *)
    log_tact "proving %a" pp_typing (Env.to_ctxt env, t, a);
    if not (check t a) then fatal tac.pos "Ill-typed refinement.";
    (* Instantiation. *)
    Meta.set m (Bindlib.unbox (Bindlib.bind_mvar (Env.vars env) (lift t)));
    (* New subgoals and focus. *)
    let metas = Basics.get_metas true t in
    let add_goal m = List.insert Goal.compare (Goal.of_meta m) in
    let new_goals = MetaSet.fold add_goal metas [] in
    (* New goals must appear first. *)
    {ps with proof_goals = new_goals @ gs}
  in

  match tac.elt with
  | P_tac_print
  | P_tac_proofterm
  | P_tac_query(_)      -> assert false (* Handled above. *)
  | P_tac_focus(i)      ->
     (* Put the [i]-th goal in focus (if possible). *)
     let rec swap i acc gs =
       match (i, gs) with
       | (0, g::gs) -> g :: List.rev_append acc gs
       | (i, g::gs) -> swap (i-1) (g::acc) gs
       | (_, _    ) -> fatal tac.pos "Invalid goal index."
     in
     {ps with proof_goals = swap i [] ps.proof_goals}
  | P_tac_refine(t)     ->
      handle_refine (scope t)
  | P_tac_intro(xs)     ->
      let t = Pos.none (P_Abst([(xs,None,false)], Pos.none P_Wild)) in
      handle_refine (scope t)
  | P_tac_apply(pt)      ->
      let t = scope pt in
      (* Infer the type of [t] and count the number of products. *)
      (* NOTE there is room for improvement here. *)
      let nb =
        match infer t with
        | Some(a) -> Basics.count_products a
        | None    ->
            fatal pt.pos "Cannot infer the type of [%a]." pp_term t
      in
      (* Refine using [t] applied to [nb] wildcards (metavariables). *)
      (* NOTE it is scoping that handles wildcards as metavariables. *)
      let rec add_wilds pt n =
        match n with
        | 0 -> scope pt
        | _ -> add_wilds (Pos.none (P_Appl(pt, Pos.none P_Wild))) (n-1)
      in
      handle_refine (add_wilds pt nb)
  | P_tac_simpl         ->
      {ps with proof_goals = Goal.simpl g :: gs}
  | P_tac_rewrite(b,po,t) ->
      let po = Option.map (Scope.scope_rw_patt ss env) po in
      handle_refine (Rewrite.rewrite ss tac.pos ps b po (scope t))
  | P_tac_refl          ->
      handle_refine (Rewrite.reflexivity ss tac.pos ps)
  | P_tac_sym           ->
      handle_refine (Rewrite.symmetry ss tac.pos ps)
  | P_tac_why3(config)  ->
      handle_refine (Why3_tactic.handle ss tac.pos config g)
  | P_tac_fail          ->
      fatal tac.pos "Call to tactic \"fail\""

let handle_tactic : Sig_state.t -> Proof.t -> p_tactic -> Proof.t =
  fun ss ps tac ->
  try handle_tactic ss ps tac
  with Fatal(_,_) as e ->
    let _ = handle_tactic ss ps (none P_tac_print) in
    raise e
