(** Calling a prover using Why3. *)

open Common
open Core
open Timed

(** [default_prover] contains the name of the current prover. Note that it can
    be changed by using the "set prover <string>" command. *)
val default_prover : string ref

(** [timeout] is the current time limit (in seconds) for a Why3 prover to find
    a proof. It can be changed with "set prover <int>". *)
val timeout : int ref

(** [handle ss pos ps prover_name gt] runs the Why3 prover corresponding to
    [prover_name] (if given or a default one otherwise) on the goal type [gt],
    and fails if no proof is found. *)
val handle: Sig_state.t -> Pos.popt -> string option -> Goal.goal_typ -> unit
