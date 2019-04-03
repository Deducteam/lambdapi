(** Toplevel commands. *)

open Extra
open Console
open Terms
open Print
open Pos
open Syntax
open Scope

(** Logging function for tactics. *)
let log_tact = new_logger 'i' "tact" "debugging information for tactics"
let log_tact = log_tact.logger

(** [handle_tactic ss ps tac] tries to apply the tactic [tac] (in the proof
     state [ps]), and returns the new proof state.  This function fails
     gracefully in case of error. *)
let handle_tactic : sig_state -> Proof.t -> p_tactic -> Proof.t =
    fun ss ps tac ->
    (* First handle the tactics that do not change the goals. *)
  match tac.elt with
  | P_tac_print         ->
      (* Just print the current proof state. *)
      Console.out 1 "%a" Proof.pp ps; ps
  | P_tac_proofterm     ->
      (* Just print the current proof term. *)
      let t = Meta(ps.Proof.proof_term, [||]) in
      let name = ps.Proof.proof_name.elt in
      Console.out 1 "Proof term for [%s]: [%a]\n" name Print.pp t; ps
  | P_tac_query(q)      ->
      Queries.handle_query ss (Some ps) q; ps
  | _                   ->
  (* The other tactics may change the goals. *)
  (* Get the focused goal and the other goals. *)
  let (g, gs) =
    match ps.Proof.proof_goals with
    | []    -> fatal tac.pos "There is nothing left to prove.";
    | g::gs -> (g, gs)
  in
  (* Obtaining the goal environment and type. *)
  let (env, a) = Proof.Goal.get_type g in

  let scope = scope_term ss env in
  let infer t = Typing.infer ss.builtins (Ctxt.of_env env) t in
  let check t a = Typing.check ss.builtins (Ctxt.of_env env) t a in

  let handle_refine : term -> Proof.t = fun t ->
    (* Check if the goal metavariable appears in [t]. *)
    let m = Proof.Goal.get_meta g in
    log_tact "refining [%a] with term [%a]" pp_meta m pp t;
    if Basics.occurs m t then fatal tac.pos "Circular refinement.";
    (* Check that [t] is well-typed. *)
    log_tact "proving [%a ⊢ %a : %a]" Ctxt.pp (Ctxt.of_env env) pp t pp a;
    if not (check t a) then fatal tac.pos "Ill-typed refinement.";
    (* Instantiation. *)
    set_meta m (Bindlib.unbox (Bindlib.bind_mvar (Env.vars env) (lift t)));
    (* New subgoals and focus. *)
    let metas = Basics.get_metas t in
    let new_goals = List.map Proof.Goal.of_meta metas in
    Proof.({ps with proof_goals = new_goals @ gs})
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
     Proof.{ps with proof_goals = swap i [] ps.proof_goals}
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
        | None    -> fatal pt.pos "Cannot infer the type of [%a]." Print.pp t
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
      Proof.({ps with proof_goals = Proof.Goal.simpl g :: gs})
  | P_tac_rewrite(po,t) ->
      let po = Option.map (scope_rw_patt ss env) po in
      handle_refine (Rewrite.rewrite tac.pos ps po (scope t))
  | P_tac_refl          ->
      handle_refine (Rewrite.reflexivity tac.pos ps)
  | P_tac_sym           ->
      handle_refine (Rewrite.symmetry tac.pos ps)
