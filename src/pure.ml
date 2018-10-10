(** Interface to lp-lsp. *)

open Timed
open Extra
open Console

(** Representation of a single command (abstract). *)
type command = Syntax.p_cmd

(** Exception raised by [parse_text] on error. *)
exception Parse_error of Pos.pos

let parse_text : string -> command Pos.loc list = fun s ->
  let parse = Earley.parse_string Parser.cmds Parser.blank in
  try parse s with Earley.Parse_error(buf, pos) ->
  raise (Parse_error(Pos.locate buf pos buf pos))

type state = Time.t * Scope.sig_state

type result =
  | OK    of state
  | Error of Pos.popt option * string

let t0 = Time.save ()

let initial_state : Files.module_path -> state = fun path ->
  Time.restore t0;
  Sign.loading := [path];
  let sign = Sign.create path in
  Sign.loaded  := Files.PathMap.add path sign !Sign.loaded;
  (Time.save (), Scope.empty_sig_state sign)

let handle_command : state -> command Pos.loc -> result = fun (st,ss) cmd ->
  Time.restore st;
  try
    let ss = Handle.new_handle_cmd ss cmd in
    OK(Time.save (), ss)
  with Fatal(p,m) -> Error(p,m)

let get_symbols : state -> (Terms.sym * Pos.popt) StrMap.t = fun (st,_) ->
  Time.restore st; !(Sign.((current_sign ()).sign_symbols))
