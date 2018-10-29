open Extra
open Timed
open Console
open Terms

(** Logging function for tactics. *)
let log_tact = new_logger 'i' "tact" "debugging information for tactics"
let log_tact = log_tact.logger

(** [handle_refine t pos ps] tries to apply the refine tactic (done on 
    line [pos]) to the proof state [ps], and returns the new proof state. *)
let handle_refine : term -> Pos.popt -> Proof.t -> Proof.t = 
  fun t pos ps ->
  let (g, gs) =
    match Proof.(ps.proof_goals) with
    | []    -> fatal pos "There is nothing left to prove.";
    | g::gs -> (g, gs)
  in
  (* Obtaining the goals environment and type. *)
  let (env, a) = Proof.Goal.get_type g in
  (* Check if the goal metavariable appears in [t]. *)
  let m = Proof.Goal.get_meta g in
  (* log_tact "refining [%a] with term [%a]" pp_meta m pp t; *)
  if Basics.occurs m t then fatal pos "Circular refinement.";
  (* Check that [t] is well-typed. *)
  let ctx = Ctxt.of_env env in
  log_tact "proving [%a ⊢ %a : %a]" Ctxt.pp ctx Print.pp t Print.pp a;
  if not (Solve.check ctx t a) then fatal pos "Ill-typed refinement.";
  (* Instantiation. *)
  let vs = Array.of_list (List.map (fun (_,(x,_)) -> x) env) in
  m.meta_value := Some(Bindlib.unbox (Bindlib.bind_mvar vs (lift t)));
  (* New subgoals and focus. *)
  let metas = Basics.get_metas t in
  let new_goals = List.rev_map Proof.Goal.of_meta_decomposed metas in
  Proof.({ps with proof_goals = new_goals @ gs})
