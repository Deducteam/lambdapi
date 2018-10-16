(** Interface to LSP *)

(* Lambdapi core *)
open Core

module Command : sig
  type t
  val equal : t -> t -> bool
  val get_pos : t -> Pos.popt
end

module Tactic : sig
  type t
  val equal : t -> t -> bool
  val get_pos : t -> Pos.popt
end

exception Parse_error of Pos.pos * string

val parse_text : string -> string -> Command.t list


type command_state

type proof_state

type command_result =
  | Cmd_OK    of command_state
  | Cmd_Proof of proof_state * Tactic.t list
  | Cmd_Error of Pos.popt option * string

type tactic_result =
  | Tac_OK    of proof_state
  | Tac_Error of Pos.popt option * string

val initial_state : Files.module_path -> command_state

val handle_command : command_state -> Command.t -> command_result

val handle_tactic : proof_state -> Tactic.t -> tactic_result

val end_proof : proof_state -> command_state

val get_symbols : command_state -> (Terms.sym * Pos.popt) Extra.StrMap.t
