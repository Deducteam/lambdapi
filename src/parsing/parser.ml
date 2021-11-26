(** Parsing functions for Lambdapi.

    This module includes two parsers: a parser for the Lambdapi syntax whose
    functions are available either through the submodule
    {!module:Parser.Lp}, or directly in {!module:Parser}; and another
    parser for the Dedukti 2.7 syntax, available through
    {!module:Parser.Dk}. *)

open! Lplib
open Base
open Common

(** [parser_fatal loc fmt] is a wrapper for [Error.fatal] that enforces
    that the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) koutfmt -> 'a = fun loc fmt ->
  Error.fatal (Some(loc)) fmt

(** [qident_of_string s] converts the string [s] into a path. *)
let qident_of_string : string -> (Syntax.qident, Pos.popt) result = fun s ->
    let lexbuf = Sedlexing.Utf8.from_string s in
    let lexer = LpLexer.lexer lexbuf in
    let parse =
      MenhirLib.Convert.Simplified.traditional2revised LpParser.id in
    try Ok(let Pos.{elt;_} = parse lexer in elt)
    with LpLexer.SyntaxError(s) -> Error(s.pos)
       | LpParser.Error ->
           let loc = Pos.locate (Sedlexing.lexing_positions lexbuf) in
           Error(Some(loc))

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
  let lp_lexbuf_fixup lexbuf fname =
    let pos = Lexing.
                { pos_fname = fname
                ; pos_lnum = 1
                ; pos_bol = 0
                ; pos_cnum = 0 } in
    Sedlexing.set_position lexbuf pos

  let stream_of_lexbuf :
    ?inchan:in_channel -> ?fname:string -> Sedlexing.lexbuf ->
    (* Input channel passed as parameter to be closed at the end of stream. *)
    Syntax.p_command Stream.t =
    fun ?inchan ?fname lexbuf ->
      Option.iter (Sedlexing.set_filename lexbuf) fname;
      Option.iter (lp_lexbuf_fixup lexbuf) fname;
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
  let stream_of_lexbuf :
    ?inchan:in_channel -> ?fname:string -> Lexing.lexbuf ->
    (* Input channel passed as parameter to be closed at the end of stream. *)
    Syntax.p_command Stream.t =
    fun ?inchan ?fname lexbuf ->
      let fn n =
        lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = n}
      in
      Option.iter fn fname;
        (*In OCaml >= 4.11: Lexing.set_filename lexbuf fname;*)
      let generator _ =
        try Some (DkParser.line DkLexer.token lexbuf)
        with
        | End_of_file -> Option.iter close_in inchan; None
        | DkParser.Error ->
            let loc =
              Lexing.(lexbuf.lex_start_p, lexbuf.lex_curr_p) in
            let loc = Pos.locate loc in
            parser_fatal loc "Unexpected token [%s]." (Lexing.lexeme lexbuf)
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
