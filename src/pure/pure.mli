(** Interface to LSP. *)

open Lplib
open Core
open Common
open Handle

(** Abstract representation of a command (top-level item). *)
module Command : sig
  type t
  val equal : t -> t -> bool
  val get_pos : t -> Pos.popt
  val print : t Base.pp [@@ocaml.toplevel_printer]
end

val rangemap : Command.t list -> Term.qident RangeMap.t

(** Abstract representation of a tactic (proof item). *)
module Tactic : sig
  type t
  val equal : t -> t -> bool
  val get_pos : t -> Pos.popt
  val print : t Base.pp [@@ocaml.toplevel_printer]
end

(** Abstract representation of a proof. *)
module ProofTree : sig
  type t
  val equal : t -> t -> bool
  val fold : ('a -> Tactic.t -> int -> 'a) -> 'a -> t -> 'a
end

(** Representation of the state when at the toplevel. *)
type state

(** Representation of the state when in a proof. *)
type proof_state

(** [parse_text ~fname contents] runs the parser on the string [contents] as
    if it were a file named [fname]. It returns the list of commands it could
    parse and, either [None] if it could parse all commands, or some position
    and error message otherwise. *)
    val parse_text :
    fname:string -> string -> Command.t list * (Pos.pos * string) option

(** [current_goals s] returns the list of open goals for proof state [s]. *)
val current_goals : proof_state -> Goal.info list

(** Result type of the [handle_command] function. *)
type command_result =
  | Cmd_OK    of state * string option
  (** Command is done. *)
  | Cmd_Proof of proof_state * ProofTree.t * Pos.popt * Pos.popt
  (** Enter proof mode (positions are for statement and qed). *)
  | Cmd_Error of Pos.popt option * string
  (** Error report. *)

(** Result type of the [handle_tactic] function. *)
type tactic_result =
  | Tac_OK    of proof_state * string option
  | Tac_Error of Pos.popt option * string

(** [initial_state fname] gives an initial state for working with the (source)
    file [fname]. The resulting state can be used by [handle_command]. *)
val initial_state : string -> state

(** [handle_command st cmd] evaluates the command [cmd] in state [st],  giving
    one of three possible results: the command is fully handled (corresponding
    to the [Cmd_OK] constructor,  the command starts a proof (corresponding to
    the [Cmd_Proof] constructor), or the command fails (corresponding  to  the
    [Cmd_Error] constuctor). *)
val handle_command : state -> Command.t -> command_result

(** [handle_tactic ps tac n] evaluates the tactic [tac] with [n] subproofs in
   proof state [ps], returning a new proof state (with [Tac_OK]) or an error
   (with [Tac_Error]). *)
val handle_tactic : proof_state -> Tactic.t -> int -> tactic_result

(** [end_proof st] finalises the proof which state is [st], returning a result
    at the command level for the whole theorem. This function should be called
    when all the tactics have been handled with [handle_tactic]. Note that the
    value returned by this function cannot be {!constructor:Cmd_Proof}. *)
val end_proof : proof_state -> command_result

(** [get_symbols st] returns all the symbols defined in the signature at state
    [st]. This can be used for displaying the type of symbols. *)
val get_symbols : state -> Term.sym Extra.StrMap.t

(** [set_initial_time ()] records the current imperative state as the rollback
    "time" for the [initial_state] function. This is only useful to initialise
    or reinitialise the pure interface. *)
val set_initial_time : unit -> unit
