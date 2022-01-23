(** Calling a prover using Why3. *)

open Common
open Core open Term
open Timed

(** [default_prover] contains the name of the current prover. Note that it can
    be changed by using the "set prover <string>" command. *)
val default_prover : string ref

(** [timeout] is the current time limit (in seconds) for a Why3 prover to find
    a proof. It can be changed with "set prover <int>". *)
val timeout : int ref

(** [handle ss pos ps prover_name g] runs the Why3 prover corresponding to the
    name [prover_name] (if given or a default one otherwise) on the goal  [g].
    If the prover succeeded to prove the goal, then this is reflected by a new
    axiom that is added to signature [ss]. *)
val handle: Sig_state.t -> Pos.popt -> string option -> Proof.goal_typ -> term
