(** Parsing functions for Lambdapi.

    This module includes two parsers: a parser for the Lambdapi syntax whose
    functions are available either through the submodule
    {!module:Parser.Lp}, or directly in {!module:Parser}; and another
    parser for the Dedukti 2.7 syntax, available through
    {!module:Parser.Dk}. *)

open! Lplib
open Common
open Module

(** [parser_fatal loc fmt] is a wrapper for [Console.fatal] that enforces
    that the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) Console.koutfmt -> 'a = fun loc fmt ->
  Console.fatal (Some(loc)) fmt

(** [add_prefix p s] adds the prefix [p] at the beginning of the
    identifier [s]. *)
let add_prefix : string -> string -> string = fun p s ->
  if is_escaped s then "{|" ^ p ^ String.(sub s 2 (length s - 4)) ^ "|}"
  else p ^ s

(** [qident_of_string s] converts the string [s] into a path. *)
let qident_of_string : string -> (Syntax.qident, Pos.popt) result = fun s ->
    let lexbuf = Sedlexing.Utf8.from_string s in
    let lexer = LpLexer.lexer lexbuf in
    let parse =
      MenhirLib.Convert.Simplified.traditional2revised LpParser.id in
    try let Pos.{elt;_} = parse lexer in Ok(elt)
    with LpLexer.SyntaxError(s) -> Error(s.pos)
       | LpParser.Error ->
           let loc = Pos.locate (Sedlexing.lexing_positions lexbuf) in
           Error(Some(loc))

(** [parse_qident s] parses the identifier [s] and returns the parsed
    identifier (with location). *)
(*let parse_qident : string -> (Syntax.qident, int * Pos.popt) result =
  fun s ->
  let parse_ident (s: string): Syntax.p_qident result =
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
  let exception Invalid_id of int * Pos.popt in
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
  with Invalid_id(i, pos) -> Error(i, pos)*)

(** Module type of a parser. *)
module type PARSER = sig
  val parse_file : string -> Syntax.ast
  (** [parse_file fname] returns a stream of parsed commands of file
      [fname]. Commands are parsed lazily. *)

  val parse_string : string -> string -> Syntax.ast
  (** [parse_string f s] retudns a stream of parsed commands from string [s]
      which comes from file [f] ([f] can be anything). *)
end

module Lp : PARSER = struct

  (* Needed to workaround serious bug in sedlex, see #549 *)
  let lp_lexbuf_fixup fname lexbuf =
    let pos = Lexing.
                { pos_fname = fname
                ; pos_lnum = 1
                ; pos_bol = 0
                ; pos_cnum = 0 } in
    Sedlexing.set_position lexbuf pos

  let stream_of_lexbuf :
    ?inchan:in_channel -> string -> Sedlexing.lexbuf ->
    (* Input channel passed as parameter to be closed at the end of stream. *)
    Syntax.p_command Stream.t =
    fun ?inchan fname lexbuf ->
      Sedlexing.set_filename lexbuf fname;
      lp_lexbuf_fixup fname lexbuf;
      let parse =
        MenhirLib.Convert.Simplified.traditional2revised LpParser.command
      in
      let lexer = LpLexer.lexer lexbuf in
      let generator _ =
        try Some(parse lexer)
        with
        | End_of_file -> Option.iter close_in inchan; None
        | LpLexer.SyntaxError(s) ->
            let loc = match s.pos with Some(l) -> l | None -> assert false in
            parser_fatal loc "Unexpected character: [%s]" s.elt
        | LpParser.Error ->
            let loc = Sedlexing.lexing_positions lexbuf in
            let loc = Pos.locate loc in
            parser_fatal loc "Unexpected token [%s]."
              (Sedlexing.Utf8.lexeme lexbuf)
      in
      Stream.from generator

  let parse_file fname =
    let inchan = open_in fname in
    stream_of_lexbuf ~inchan fname (Sedlexing.Utf8.from_channel inchan)

  let parse_string fname s =
    stream_of_lexbuf fname (Sedlexing.Utf8.from_string s)
end

(** Parsing legacy (Dedukti2) syntax. *)
module Dk : PARSER = struct
  let stream_of_lexbuf :
    ?inchan:in_channel -> string -> Lexing.lexbuf ->
    (* Input channel passed as parameter to be closed at the end of stream. *)
    Syntax.p_command Stream.t =
    fun ?inchan fname lexbuf ->
      DkLexer.filename := fname;
      let generator _ =
        try Some(DkParser.command DkLexer.token lexbuf)
        with
        | End_of_file -> Option.iter close_in inchan; None
        | DkParser.Error ->
            let loc =
              Lexing.(lexbuf.lex_start_p, lexbuf.lex_curr_p) in
            let loc = Pos.locate loc in
            parser_fatal loc "Unexpected token [%s]." (Lexing.lexeme lexbuf)
      in
      Stream.from generator

  let parse_file fname =
    let inchan = open_in fname in
    let lexbuf = Lexing.from_channel inchan in
    try stream_of_lexbuf ~inchan fname lexbuf
    with e -> close_in inchan; raise e

  let parse_string fname s = stream_of_lexbuf fname (Lexing.from_string s)
end

(* Include parser of new syntax so that functions are directly available.*)
include Lp
