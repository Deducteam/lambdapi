(** Interface to LSP *)

(* Lambdapi core *)
open Core

module Command : sig
  type t
  val equal : t -> t -> bool
end

type state

exception Parse_error of Pos.pos * string

val parse_text : string -> string -> Command.t Pos.loc list

type result =
  | OK    of state
  | Error of Pos.popt option * string

val initial_state : Files.module_path -> state

val handle_command : state -> Command.t Pos.loc -> result

val get_symbols : state -> (Terms.sym * Pos.popt) Extra.StrMap.t
