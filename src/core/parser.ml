(** Parsing functions for Lambdapi.

    This module includes two parsers: a parser for the Lambdapi syntax whose
    functions are available either through the submodule
    {!module:Parser.Lp}, or directly in {!module:Parser}; and another
    parser for the Dedukti 2.7 syntax, available through
    {!module:Parser.Dk}. *)

open! Lplib
open Pos

(** [parser_fatal loc fmt] is a wrapper for [Console.fatal] that enforces
    that the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) Console.koutfmt -> 'a = fun loc fmt ->
  Console.fatal (Some(loc)) fmt

(** [add_prefix p s] adds the prefix [p] at the beginning of the
    identifier [s]. *)
let add_prefix : string -> string -> string = fun p s ->
  let n = String.length s in
  if n >= 4 && s.[0] ='{' && s.[1] = '|' then
    "{|" ^ p ^ String.sub s 2 (n-4) ^ "|}"
  else
    p ^ s

(** Module type of a parser. *)
module type PARSER = sig

  val parse_file : string -> Syntax.ast
  (** [parse_file s] parses file at path [s]. *)

  val parse_string : string -> string -> Syntax.ast
  (** [parse_string f s] parses string [s] comming from file [f] ([f] can be
      anything). *)
end

module Lp : PARSER = struct
  let parse_lexbuf : string -> Sedlexing.lexbuf -> Syntax.ast =
    fun fname lexbuf ->
    Sedlexing.set_filename lexbuf fname;
    let parse =
      MenhirLib.Convert.Simplified.traditional2revised LpParser.command
    in
    let lexer = LpLexer.lexer lexbuf in
    let cmds = ref [] in
    try
      while true do
        let cmd = parse lexer in
        cmds := cmd :: !cmds;
      done;
      assert false (* Should raise end of file before *)
    with
    | End_of_file -> List.rev !cmds
    | LpLexer.SyntaxError(s) ->
        let loc = match s.pos with Some(l) -> l | None -> assert false in
        parser_fatal loc "Unexpected character: [%s]" s.elt
    | LpParser.Error ->
        let loc = Sedlexing.lexing_positions lexbuf in
        let loc = Pos.locate loc in
        parser_fatal loc "Unexpected token [%s]."
          (Sedlexing.Utf8.lexeme lexbuf)

  let parse_file : string -> Syntax.ast = fun fname ->
    let inchan = open_in fname in
    let res = parse_lexbuf fname (Sedlexing.Utf8.from_channel inchan) in
    close_in inchan;
    res

  let parse_string : string -> string -> Syntax.ast = fun fname s ->
    parse_lexbuf fname (Sedlexing.Utf8.from_string s)
end

(** [parse_qident s] parses the identifier [s] and returns the parsed
    identifier (with location) and a boolean being [true] if [s] is
    escaped (with [{| |}]). We use [parse_ident] of menhir parser because
    exposing [parse_qident] caused an end of stream conflict. *)
let parse_qident : string ->
  (Syntax.p_module_path * string, int * popt) result =
  fun s ->
  let parse_ident (s: string): (Syntax.ident * bool, popt) result =
    let parse =
      MenhirLib.Convert.Simplified.traditional2revised LpParser.ident
    in
    let lexbuf = Sedlexing.Utf8.from_string s in
    let lexer = LpLexer.lexer lexbuf in
    try Ok(parse lexer)
    with LpLexer.SyntaxError(s) -> Error(s.pos)
       | LpParser.Error ->
         let loc = Pos.locate (Sedlexing.lexing_positions lexbuf) in
         Error(Some(loc))
  in
  (* We get individual identifiers. *)
  let ids = String.split_on_char '.' s in
  (* Here we'd like a bind operation on result: if there is an error. *)
  let exception Invalid_id of int * popt in
  let f (i: int) (e: string) =
    (* Parse string [e] and raise error to interrupt if [e] is not valid. *)
    let (e, b) =
      match parse_ident e with
      | Ok(e, b) -> (e, b)
      | Error(pos) -> raise (Invalid_id(i, pos))
    in
    (e.Pos.elt, b)
  in
  try
    let ids = List.mapi f ids in
    let (ids, last) = List.split_last ids in
    Ok(ids, fst last)
with Invalid_id(i, pos) -> Error(i, pos)

(** Parsing legacy (Dedukti2) syntax. *)
module Dk : PARSER = struct
  let parse_lexbuf : string -> Lexing.lexbuf -> Syntax.ast =
    fun fname lexbuf ->
    Stdlib.(DkLexer.filename := fname);
    let lines = ref [] in
    try
      while true do
        let l = DkParser.line DkLexer.token lexbuf in
        lines := l :: !lines
      done;
      assert false (* Unreachable. *)
    with
    | End_of_file -> List.rev !lines
    | DkParser.Error ->
        let loc =
          Lexing.(lexbuf.lex_start_p, lexbuf.lex_curr_p) in
        let loc = Pos.locate loc in
        parser_fatal loc "Unexpected token [%s]." (Lexing.lexeme lexbuf)

  let parse_file : string -> Syntax.ast = fun fname ->
    let ic = open_in fname in
    let lexbuf = Lexing.from_channel ic in
    try let l = parse_lexbuf fname lexbuf in close_in ic; l
    with e -> close_in ic; raise e

  let parse_string : string -> string -> Syntax.ast = fun fname s ->
    parse_lexbuf fname (Lexing.from_string s)
end

(* Include parser of new syntax so that functions are directly available.*)
include Lp
