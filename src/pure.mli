(** Interface to PLOF. *)

type command = Parser.p_cmd Pos.loc
type state

type result =
  | OK    of state
  | Error of Pos.popt option * string

val initial_state : Files.module_path -> state

val handle_command : state -> command -> result

val in_state : state -> ('a -> 'b) -> 'a -> 'b
