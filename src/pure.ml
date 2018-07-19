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
  | Error of Pos.popt option * string

let t0 = Time.save ()

let initial_state : Files.module_path -> state = fun path ->
  Time.restore t0;
  Sign.loading := [path];
  Sign.loaded  := Files.PathMap.add path (Sign.create path) !Sign.loaded;
  Time.save ()

let handle_command : state -> command -> result = fun t cmd ->
  Time.restore t;
  try handle_cmd cmd; OK(Time.save ()) with Fatal(p,m) -> Error(p,m)
