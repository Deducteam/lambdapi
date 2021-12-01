(** Parsing functions for Lambdapi.

    This module includes two parsers: a parser for the Lambdapi syntax whose
    functions are available either through the submodule
    {!module:Parser.Lp}, or directly in {!module:Parser}; and another
    parser for the Dedukti 2.7 syntax, available through
    {!module:Parser.Dk}. *)

open! Lplib
open Base
open Common

(** [parser_fatal pos fmt] is a wrapper for [Error.fatal] that enforces
    that the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) koutfmt -> 'a = fun pos fmt ->
  Error.fatal (Some(pos)) fmt

(** [qident_of_string s] converts the string [s] into a path. *)
let qident_of_string : string -> (Syntax.qident, Pos.popt) result = fun s ->
    let lb = Sedlexing.Utf8.from_string s in
    let token = LpLexer.token lb in
    let parse =
      MenhirLib.Convert.Simplified.traditional2revised LpParser.id in
    try Ok(let Pos.{elt;_} = parse token in elt)
    with LpLexer.SyntaxError(s) -> Error(s.pos)
       | LpParser.Error ->
           Error(Some(Pos.locate (Sedlexing.lexing_positions lb)))

(** Module type of a parser. *)
module type PARSER = sig

  val parse : in_channel -> Syntax.ast
  (** [parse inchan] returns a stream of commands parsed from
      channel [inchan]. Commands are parsed lazily and the channel is
      closed once all entries are parsed. *)

  val parse_file : string -> Syntax.ast
  (** [parse_file fname] returns a stream of parsed commands of file
      [fname]. Commands are parsed lazily. *)

  val parse_string : string -> string -> Syntax.ast
  (** [parse_string f s] returns a stream of parsed commands from string [s]
      which comes from file [f] ([f] can be anything). *)
end

module Lp : PARSER = struct

  (* Needed to workaround serious bug in sedlex, see #549 *)
  let lexbuf_fixup lb fname =
    let pos = Lexing.
                { pos_fname = fname
                ; pos_lnum = 1
                ; pos_bol = 0
                ; pos_cnum = 0 } in
    Sedlexing.set_position lb pos

  let stream_of_lexbuf :
    ?inchan:in_channel -> ?fname:string -> Sedlexing.lexbuf ->
    (* Input channel passed as parameter to be closed at the end of stream. *)
    Syntax.p_command Stream.t =
    fun ?inchan ?fname lb ->
      Option.iter (Sedlexing.set_filename lb) fname;
      Option.iter (lexbuf_fixup lb) fname;
      let parse =
        MenhirLib.Convert.Simplified.traditional2revised LpParser.command
      in
      let token = LpLexer.token lb in
      let generator _ =
        try Some(parse token)
        with
        | End_of_file -> Option.iter close_in inchan; None
        | LpLexer.SyntaxError {pos=None; _} -> assert false
        | LpLexer.SyntaxError {pos=Some pos; elt} -> parser_fatal pos "%s" elt
        | LpParser.Error ->
            let pos = Pos.locate (Sedlexing.lexing_positions lb) in
            parser_fatal pos
              "Unexpected character: %s" (Sedlexing.Utf8.lexeme lb)
      in
      Stream.from generator

  let parse inchan =
    stream_of_lexbuf ~inchan (Sedlexing.Utf8.from_channel inchan)

  let parse_file fname =
    let inchan = open_in fname in
    stream_of_lexbuf ~inchan ~fname (Sedlexing.Utf8.from_channel inchan)

  let parse_string fname s =
    stream_of_lexbuf ~fname (Sedlexing.Utf8.from_string s)
end

(** Parsing legacy (Dedukti2) syntax. *)
module Dk : PARSER = struct

  let token : Lexing.lexbuf -> DkTokens.token =
    let r = ref DkTokens.EOF in fun lb ->
    Debug.(record_time Lexing (fun () -> r := DkLexer.token lb)); !r

  let command :
    (Lexing.lexbuf -> DkTokens.token) -> Lexing.lexbuf -> Syntax.p_command =
    let r = ref (Pos.none (Syntax.P_open [])) in fun token lb ->
    Debug.(record_time Parsing (fun () -> r := DkParser.line token lb)); !r

  let stream_of_lexbuf :
    ?inchan:in_channel -> ?fname:string -> Lexing.lexbuf ->
    (* Input channel passed as parameter to be closed at the end of stream. *)
    Syntax.p_command Stream.t =
    fun ?inchan ?fname lb ->
      let fn n =
        lb.lex_curr_p <- {lb.lex_curr_p with pos_fname = n}
      in
      Option.iter fn fname;
        (*In OCaml >= 4.11: Lexing.set_filename lb fname;*)
      let generator _ =
        try Some (command token lb)
        with
        | End_of_file -> Option.iter close_in inchan; None
        | DkParser.Error ->
            let pos = Pos.locate (Lexing.(lb.lex_start_p, lb.lex_curr_p)) in
            parser_fatal pos "Unexpected token [%s]." (Lexing.lexeme lb)
      in
      Stream.from generator

  let parse inchan =
    try stream_of_lexbuf ~inchan (Lexing.from_channel inchan)
    with e -> close_in inchan; raise e

  let parse_file fname =
    let inchan = open_in fname in
    stream_of_lexbuf ~inchan ~fname (Lexing.from_channel inchan)

  let parse_string fname s = stream_of_lexbuf ~fname (Lexing.from_string s)
end

(* Include parser of new syntax so that functions are directly available.*)
include Lp
