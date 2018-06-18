(** Interface to PLOF. *)

open Handle
open Console
open Parser
open Pos
open Timed

type command = p_cmd loc

type state = Time.t

type result =
  | OK    of state
  | Error of string

let initial_state : state = Time.save ()

let handle_command : state -> command -> result = fun t cmd ->
  Time.rollback t;
  try handle_cmd cmd; OK(Time.save ()) with Fatal(m) -> Error(m)
