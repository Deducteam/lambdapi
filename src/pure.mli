(** Interface to PLOF. *)

type command
type state

exception Parse_error of Pos.pos
val parse_text : string -> command Pos.loc list

type result =
  | OK    of state
  | Error of Pos.popt option * string

val initial_state : Files.module_path -> state

val handle_command : state -> command Pos.loc -> result

val get_symbols : state -> (Terms.sym * Pos.popt) Extra.StrMap.t
