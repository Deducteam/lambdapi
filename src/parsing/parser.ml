(** Parsing functions for Lambdapi.

    This module includes two parsers: a parser for the Lambdapi syntax whose
    functions are available either through the submodule {!module:Parser.Lp}
    or directly in {!module:Parser}, and a parser for the Dedukti syntax
    available through {!module:Parser.Dk}. *)

open Lplib open Base
open Common
open Syntax
open Lexing

type lexpos = Lexing.position

(** [parser_fatal pos fmt] is a wrapper for [Error.fatal] that enforces
    that the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) koutfmt -> 'a = fun pos fmt ->
  Error.fatal (Some(pos)) fmt

(** Module type of a parser. *)
module type PARSER = sig
  val parse_in_channel : in_channel -> ast
  (** [parse ic] returns a stream of commands parsed from
      channel [ic]. Commands are parsed lazily and the channel is
      closed once all entries are parsed. *)

  val parse_file : string -> ast
  (** [parse_file fname] returns a stream of parsed commands of file
      [fname]. Commands are parsed lazily. *)

  val parse_string : string -> string -> ast
  (** [parse_string f s] returns a stream of parsed commands from string [s]
      which comes from file [f] ([f] can be anything). *)
end

(** Parsing dk syntax. *)
module Dk : PARSER = struct

  open Lexing

  (* defined in OCaml >= 4.11 only *)
  let set_filename (lb:lexbuf) (fname:string): unit =
    lb.lex_curr_p <- {lb.lex_curr_p with pos_fname = fname}

  (* old code:
  let parse_lexbuf :
        ?ic:in_channel -> ?fname:string -> lexbuf -> p_command Stream.t =
    fun ?ic ?fname lb ->
    Option.iter (set_filename lb) fname;
    let generator _ =
      try Some (command lb)
      with
      | End_of_file -> Option.iter close_in ic; None
      | DkParser.Error ->
          let pos = Pos.locate (lb.lex_start_p, lb.lex_curr_p) in
          parser_fatal pos "Unexpected token \"%s\"." (lexeme lb)
    in
    Stream.from generator

  let parse_string fname s = parse_lexbuf ~fname (from_string s)

  let parse_in_channel ic =
    try parse_lexbuf ~ic (from_channel ic)
    with e -> close_in ic; raise e

  let parse_file fname =
    let ic = open_in fname in
    parse_lexbuf ~ic ~fname (from_channel ic)*)

  let parse_lexbuf (icopt:in_channel option) (entry:lexbuf -> 'a) (lb:lexbuf)
      : 'a Stream.t =
    let generator _ =
      try Some(entry lb)
      with
      | End_of_file -> Option.iter close_in icopt; None
      | DkParser.Error ->
          let pos = Pos.locate (lb.lex_start_p, lb.lex_curr_p) in
          parser_fatal pos "Unexpected token \"%s\"." (lexeme lb)
    in
    Stream.from generator

  let parse_in_channel (entry:lexbuf -> 'a) (ic:in_channel): 'a Stream.t =
    parse_lexbuf (Some ic) entry (from_channel ic)

  let parse_file entry fname = parse_in_channel entry (open_in fname)

  let parse_string (entry: lexbuf -> 'a) (fname:string) (s:string)
      : 'a Stream.t =
    let lb = from_string s in
    set_filename lb fname;
    parse_lexbuf None entry lb

  let command =
    let r = ref (Pos.none (P_open [])) in
    fun (lb:lexbuf): p_command ->
    Debug.(record_time Parsing
             (fun () -> r := DkParser.line DkLexer.token lb)); !r

  (* exported functions *)
  let parse_string = parse_string command
  let parse_in_channel = parse_in_channel command
  let parse_file = parse_file command

end

(** Parsing lp syntax. *)
module Lp :
sig
  include PARSER

  val parse_search_query_string :
    string -> string -> SearchQuerySyntax.query Stream.t
  (** [parse_search_query_string f s] returns a stream of parsed terms from
      string [s] which comes from file [f] ([f] can be anything). *)

  end
= struct

  open LpLexer
  open Sedlexing

  (* old Menhir parser *)

  type tokenizer = unit -> token * lexpos * lexpos
  type 'a parser = tokenizer -> 'a

  let parse_lexbuf :
    grammar_entry:(token,'b) MenhirLib.Convert.traditional ->
    ?ic:in_channel -> ?fname:string -> lexbuf ->
    (* Input channel passed as parameter to be closed at the end of stream. *)
    'a Stream.t =
    fun ~grammar_entry ?ic ?fname lb ->
      Option.iter (set_filename lb) fname;
      let parse: 'a parser =
        MenhirLib.Convert.Simplified.traditional2revised grammar_entry in
      let token = LpLexer.token lb in
      let generator _ =
        try Some (parse token)
        with
        | End_of_file -> Option.iter close_in ic; None
        | SyntaxError {pos=None; _} -> assert false
        | SyntaxError {pos=Some pos; elt} -> parser_fatal pos "%s" elt
        | LpParser.Error ->
            let pos = Pos.locate (lexing_positions lb) in
            parser_fatal pos "Unexpected token: \"%s\"." (Utf8.lexeme lb)
      in
      Stream.from generator

  let parse_string ~grammar_entry fname s =
    parse_lexbuf ~grammar_entry ~fname (Utf8.from_string s)

  let parse_search_query_string =
    parse_string ~grammar_entry:LpParser.search_query_alone

  (*let parse_in_channel ~grammar_entry ic =
    parse_lexbuf ~grammar_entry ~ic (Utf8.from_channel ic)

  let parse_file ~grammar_entry fname =
    let ic = open_in fname in
    parse_lexbuf ~grammar_entry ~ic ~fname (Utf8.from_channel ic)

  let parse_in_channel = parse_in_channel ~grammar_entry:LpParser.command
  let parse_file fname = parse_file ~grammar_entry:LpParser.command fname
  let parse_string = parse_string ~grammar_entry:LpParser.command*)

  (* new parser *)

  let parse_lexbuf icopt entry lb =
    let generator _ =
      try Some(entry lb)
      with
      | End_of_file -> Option.iter close_in icopt; None
      | SyntaxError{pos=None; _} -> assert false
      | SyntaxError{pos=Some pos; elt} -> parser_fatal pos "%s" elt
    in
    Stream.from generator

  let parse_string entry fname s =
    let lb = Utf8.from_string s in
    set_filename lb fname;
    parse_lexbuf None entry lb

  let parse_in_channel entry ic =
    parse_lexbuf (Some ic) entry (Utf8.from_channel ic)

  (*let parse_file entry fname =
    let ic = open_in fname in
    let lb = Utf8.from_channel ic in
    set_filename lb fname; (* useful? *)
    let x = parse_lexbuf entry lb in
    close_in ic;
    x*)

  let parse_file entry fname = parse_in_channel entry (open_in fname)

  (* exported functions *)
  let parse_string = parse_string Ll1.command
  let parse_in_channel = parse_in_channel Ll1.command
  let parse_file = parse_file Ll1.command

end

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
let parse_file : string -> ast = fun fname ->
  match Filename.check_suffix fname Library.lp_src_extension with
  | true  -> Lp.parse_file fname
  | false -> Dk.parse_file fname
