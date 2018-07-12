(** Proofs and tactics. *)

open Timed
open Terms
open Console

(** Representation of a goal. *)
type goal =
  { g_meta : meta
  ; g_hyps : Env.t
  ; g_type : term }
(* NOTE: [g_hyps] and [g_type] are a decomposition of the type of [g_meta]. *)

(** Representation of a theorem. *)
type theorem =
  { t_name : Pos.strloc
  ; t_proof : meta
  ; t_goals : goal list (* focused goal at the head. *) }

(** [remove_goal g gs] removes goal [g] from the list of goals [gs]. *)
let remove_goal (g:goal) (gs:goal list) : goal list =
  let rec aux gs =
    match gs with
    | [] -> []
    | g'::gs -> if g' == g then gs else g'::aux gs
  in aux gs

(** [replace_goal g1 g2 gs] replaces [g] by [g'] in [gs]. *)
let replace_goal (g1:goal) (g2:goal) (gs:goal list) : goal list =
  let rec aux gs =
    match gs with
    | [] -> []
    | g::gs -> if g == g1 then g2::gs else g::aux gs
  in aux gs

(** [theorem] contains the theorem the user is trying to prove. *)
let theorem : theorem option ref = ref None

(** [current_theorem ()] returns the current theorem if we are in a
    proof. It fails otherwise. *)
let current_theorem () : theorem =
  (* We check that we are in a proof. *)
  match !theorem with
  | None     -> fatal_no_pos "not in a proof"
  | Some thm -> thm

(** [fail_if_in_proof()] fails we are in a proof. Does nothing otherwise. *)
let fail_if_in_proof() : unit =
  match !theorem with
  | None     -> ()
  | Some _ -> fatal_no_pos "in a proof"

(** [focus_goal_hyps ()] returns the hypotheses of the currently
    focused goal if we are in a proof, or the empty list otherwise. *)
let focus_goal_hyps () : Env.t =
  match !theorem with
  | Some{t_goals = g::_} -> g.g_hyps
  | _                    -> Env.empty
