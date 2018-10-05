(** Interface to lp-lsp. *)

open Timed
open Extra
open Console

(** Representation of a single command (abstract). *)
type command = Parser.p_cmd

(** Exception raised by [parse_text] on error. *)
exception Parse_error of Pos.pos

let parse_text : string -> command Pos.loc list = fun s ->
  let parse = Earley.parse_string Parser.cmd_list Parser.blank in
  try parse s with Earley.Parse_error(buf, pos) ->
  raise (Parse_error(Pos.locate buf pos buf pos))

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

let handle_command : state -> command Pos.loc -> result = fun t cmd ->
  Time.restore t;
  try Handle.handle_cmd cmd; OK(Time.save ()) with Fatal(p,m) -> Error(p,m)

let get_symbols : state -> (Terms.sym * Pos.popt) StrMap.t = fun st ->
  Time.restore st; !(Sign.((current_sign ()).symbols))
