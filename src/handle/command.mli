open Parsing
open Core
open Proof
open Sig_state
open Syntax
open Common.Pos

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
val too_long : float Stdlib.ref

(** Type alias for a function that compiles a Lambdapi module. *)
type compiler = Common.Path.t -> Sign.t

(** Representation of a yet unchecked proof. The structure is initialized when
    the proof mode is entered, and its finalizer is called when the proof mode
    is exited (i.e., when a terminator like “end” is used).  Note that tactics
    do not work on this structure directly,  although they act on the contents
    of its [pdata_p_state] field. *)
type proof_data =
  { pdata_stmt_pos : popt (** Position of the declared symbol. *)
  ; pdata_p_state  : proof_state (** Proof state. *)
  ; pdata_tactics  : p_tactic list (** Tactics. *)
  ; pdata_finalize : sig_state -> proof_state -> sig_state (** Finalizer. *)
  ; pdata_end_pos  : popt (** Position of the proof's terminator. *)
  ; pdata_prv      : bool (** [true] iff private symbols are allowed. *) }

(** [get_proof_data compile ss cmd] tries to handle the command [cmd] with
    [ss] as the signature state and [compile] as the main compilation function
    processing lambdapi modules (it is passed as argument to avoid cyclic
    dependencies). On success, an updated signature state is returned.  When
    [cmd] leads to entering the proof mode,  a [proof_data] is also  returned.
    This structure contains the list of the tactics to be executed, as well as
    the initial state of the proof.  The checking of the proof is then handled
    separately. Note that [Fatal] is raised in case of an error. *)
val get_proof_data : compiler -> sig_state -> p_command ->
  sig_state * proof_data option * Query.result

(** [handle compile_mod ss cmd] retrieves proof data from [cmd] (with
    {!val:get_proof_data}) and handles proofs using functions from
    {!module:Tactic} The function [compile_mod] is used to compile required
    modules recursively. *)
val handle : compiler -> sig_state -> p_command -> sig_state
