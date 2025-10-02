(** Parsing functions for Lambdapi.

    This module includes two parsers: a parser for the Lambdapi syntax whose
    functions are available either through the submodule {!module:Parser.Lp}
    or directly in {!module:Parser}, and a parser for the Dedukti syntax
    available through {!module:Parser.Dk}. *)

open Lplib open Base
open Common

(** [parser_fatal pos fmt] is a wrapper for [Error.fatal] that enforces
    that the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) koutfmt -> 'a = fun pos fmt ->
  Error.fatal (Some(pos)) fmt

(** Module type of a parser. *)
module type PARSER = sig
  type lexbuf

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

  val parse_from_lexbuf : lexbuf -> Syntax.ast
  (** [parse_from_lexbuf lexbuf] is the same than [parse_string] but with an
      already created lexbuf *)

end

module Lp :
sig
  include PARSER with type lexbuf := Sedlexing.lexbuf

  val parse_term : in_channel -> Syntax.p_term Stream.t
  (** [parse inchan] returns a stream of terms parsed from
      channel [inchan]. Terms are parsed lazily and the channel is
      closed once all entries are parsed. *)

  val parse_term_file : string -> Syntax.p_term Stream.t
  (** [parse_file fname] returns a stream of parsed terms of file
      [fname]. Terms are parsed lazily. *)

  val parse_term_string : string -> string -> Syntax.p_term Stream.t
  (** [parse_term_string f s] returns a stream of parsed terms from string [s]
      which comes from file [f] ([f] can be anything). *)

  val parse_rwpatt_string : string -> string -> Syntax.p_rw_patt Stream.t
  (** [parse_rwpatt_string f s] returns a stream of parsed rewrite pattern
      specifications from string [s] which comes from file [f] ([f] can be
      anything). *)

  val parse_search_query_string :
    string -> string -> SearchQuerySyntax.query Stream.t
  (** [parse_search_query_string f s] returns a stream of parsed terms from
      string [s] which comes from file [f] ([f] can be anything). *)

  val parse_qid : string -> Core.Term.qident

  val parse_from_lexbuf : Sedlexing.lexbuf -> Syntax.ast
  (** [parse_from_lexbuf lexbuf] Same than [parse_string] but with an already created lexbuf *)

  end
= struct

  let stream_of_lexbuf :
    grammar_entry:(LpLexer.token,'b) MenhirLib.Convert.traditional ->
    ?inchan:in_channel -> ?fname:string -> Sedlexing.lexbuf ->
    (* Input channel passed as parameter to be closed at the end of stream. *)
    'a Stream.t =
    fun ~grammar_entry ?inchan ?fname lb ->
      Option.iter (Sedlexing.set_filename lb) fname;
      let parse =
        MenhirLib.Convert.Simplified.traditional2revised
         grammar_entry
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
            parser_fatal pos "Unexpected token: \"%s\"."
              (Sedlexing.Utf8.lexeme lb)
      in
      Stream.from generator

  let parse ~grammar_entry inchan =
    stream_of_lexbuf ~grammar_entry ~inchan
      (Sedlexing.Utf8.from_channel inchan)

  let parse_file ~grammar_entry fname =
    let inchan = open_in fname in
    stream_of_lexbuf ~grammar_entry ~inchan ~fname
     (Sedlexing.Utf8.from_channel inchan)

  let parse_string ~grammar_entry fname s =
    stream_of_lexbuf ~grammar_entry ~fname (Sedlexing.Utf8.from_string s)

  let parse_from_lexbuf ~grammar_entry lexbuf =
    stream_of_lexbuf ~grammar_entry ?fname:None lexbuf

  let parse_term = parse ~grammar_entry:LpParser.term_alone
  let parse_term_string = parse_string ~grammar_entry:LpParser.term_alone
  let parse_rwpatt_string =
    parse_string ~grammar_entry:LpParser.rw_patt_spec_alone
  let parse_search_query_string =
    parse_string ~grammar_entry:LpParser.search_query_alone
  let parse_term_file = parse_file ~grammar_entry:LpParser.term_alone

  let parse_qid s =
   let stream = parse_string ~grammar_entry:LpParser.qid_alone "LPSearch" s in
   (Stream.next stream).elt

  let parse = parse ~grammar_entry:LpParser.command
  let parse_string = parse_string ~grammar_entry:LpParser.command
  let parse_file = parse_file ~grammar_entry:LpParser.command

  let parse_from_lexbuf = parse_from_lexbuf ~grammar_entry:LpParser.command

end

(** Parsing dk syntax. *)
module Dk : PARSER with type lexbuf := Lexing.lexbuf = struct

  let token : Lexing.lexbuf -> DkTokens.token =
    let r = ref DkTokens.EOF in fun lb ->
    Debug.(record_time Lexing (fun () -> r := DkLexer.token lb)); !r

  let command :
    (Lexing.lexbuf -> DkTokens.token) -> Lexing.lexbuf -> Syntax.p_command =
    let r = ref (Pos.none (Syntax.P_open(false,[]))) in fun token lb ->
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
            parser_fatal pos "Unexpected token \"%s\"." (Lexing.lexeme lb)
      in
      Stream.from generator

  let parse inchan =
    try stream_of_lexbuf ~inchan (Lexing.from_channel inchan)
    with e -> close_in inchan; raise e

  let parse_file fname =
    let inchan = open_in fname in
    stream_of_lexbuf ~inchan ~fname (Lexing.from_channel inchan)

  let parse_string fname s = stream_of_lexbuf ~fname (Lexing.from_string s)

  let parse_from_lexbuf lexbuf = stream_of_lexbuf ?fname:None lexbuf
end

(* Include parser of new syntax so that functions are directly available.*)
include Lp

(** [path_of_string s] converts the string [s] into a path. *)
let path_of_string : string -> Path.t = fun s ->
  let open LpLexer in
  let lb = Sedlexing.Utf8.from_string s in
  try
    begin match token lb () with
      | UID s, _, _ -> [s]
      | QID p, _, _ -> List.rev p
      | _ -> Error.fatal_no_pos "\"%s\" is not a path." s
    end
  with SyntaxError _ -> Error.fatal_no_pos "\"%s\" is not a path." s

(** [qident_of_string s] converts the string [s] into a qident. *)
let qident_of_string : string -> Core.Term.qident = fun s ->
  let open LpLexer in
  let lb = Sedlexing.Utf8.from_string s in
  try
    begin match token lb () with
      | QID [], _, _ -> assert false
      | QID (s::p), _, _ -> (List.rev p, s)
      | _ -> Error.fatal_no_pos "\"%s\" is not a qualified identifier." s
    end
  with SyntaxError _ ->
    Error.fatal_no_pos "\"%s\" is not a qualified identifier." s

(** [parse_file fname] selects and runs the correct parser on file [fname], by
    looking at its extension. *)
let parse_file : string -> Syntax.ast = fun fname ->
  match Filename.check_suffix fname Library.lp_src_extension with
  | true  -> Lp.parse_file fname
  | false -> Dk.parse_file fname
