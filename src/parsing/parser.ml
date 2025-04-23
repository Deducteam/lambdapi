(** Parsing functions for Lambdapi.

    This module includes two parsers: a parser for the Lambdapi syntax whose
    functions are available either through the submodule {!module:Parser.Lp}
    or directly in {!module:Parser}, and a parser for the Dedukti syntax
    available through {!module:Parser.Dk}. *)

open Lplib open Base
open Common
open Syntax
open Lexing

(** [parser_fatal pos fmt] is a wrapper for [Error.fatal] that enforces
    that the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) koutfmt -> 'a = fun pos fmt ->
  Error.fatal (Some(pos)) fmt

(** Module type of a parser. *)
module type PARSER = sig
  val parse_in_channel : string -> in_channel -> ast
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

(* defined in OCaml >= 4.11 only *)
let set_filename (lb:lexbuf) (fname:string): unit =
  lb.lex_curr_p <- {lb.lex_curr_p with pos_fname = fname}

(** Parsing dk syntax. *)
module Dk : PARSER = struct

  open Lexing

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

  let parse_lexbuf (fname:string) (icopt:in_channel option)
        (entry:lexbuf -> 'a) (lb:lexbuf) : 'a Stream.t =
    set_filename lb fname;
    let generator _ =
      try Some(entry lb)
      with
      | End_of_file -> Option.iter close_in icopt; None
      | DkParser.Error ->
          let pos = Pos.locate (lb.lex_start_p, lb.lex_curr_p) in
          parser_fatal pos "Unexpected token \"%s\"." (lexeme lb)
    in
    Stream.from generator

  let parse_in_channel (entry:lexbuf -> 'a) (fname:string) (ic:in_channel)
      : 'a Stream.t =
    parse_lexbuf fname (Some ic) entry (from_channel ic)

  let parse_file entry fname = parse_in_channel entry fname (open_in fname)

  let parse_string (entry: lexbuf -> 'a) (fname:string) (s:string)
      : 'a Stream.t =
    parse_lexbuf "" None entry (from_string s)

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

open LpLexer
open Sedlexing

(** Parsing lp syntax. *)
module Lp :
sig
  include PARSER

  val parse_search_query_string : (*fname*)string -> (*query*)string -> query

  end
= struct

  (* old Menhir parser *)

  type tokenizer = unit -> token * position * position
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
        | SyntaxError {pos=Some pos; elt} ->
            parser_fatal pos "Syntax error. %s" elt
        | LpParser.Error ->
            let pos = Pos.locate (lexing_positions lb) in
            parser_fatal pos "Unexpected token: \"%s\"." (Utf8.lexeme lb)
      in
      Stream.from generator

  let parse_string ~grammar_entry fname s =
    parse_lexbuf ~grammar_entry ~fname (Utf8.from_string s)

  (*let parse_search_query_string =
    parse_string ~grammar_entry:LpParser.search_query_alone*)

  (*let parse_in_channel ~grammar_entry ic =
    parse_lexbuf ~grammar_entry ~ic (Utf8.from_channel ic)

  let parse_file ~grammar_entry fname =
    let ic = open_in fname in
    parse_lexbuf ~grammar_entry ~ic ~fname (Utf8.from_channel ic)

  let parse_in_channel = parse_in_channel ~grammar_entry:LpParser.command
  let parse_file fname = parse_file ~grammar_entry:LpParser.command fname
  let parse_string = parse_string ~grammar_entry:LpParser.command*)

  (* new parser *)

  let parse_lexbuf (fname:string) (icopt: in_channel option)
        (entry: lexbuf -> 'a) (lb: lexbuf): 'a Stream.t =
    set_filename lb fname;
    let generator _ =
      try Some(entry lb)
      with
      | End_of_file -> Option.iter close_in icopt; None
      | SyntaxError{pos=None; _} -> assert false
      | SyntaxError{pos=Some pos; elt} ->
          parser_fatal pos "Syntax error. %s" elt
    in
    Stream.from generator

  let parse_string (entry: lexbuf -> 'a) (fname: string) (s: string)
      : 'a Stream.t =
    parse_lexbuf fname None entry (Utf8.from_string s)

  let parse_in_channel (entry: lexbuf -> 'a) (fname:string) (ic: in_channel)
      : 'a Stream.t =
    parse_lexbuf fname (Some ic) entry (Utf8.from_channel ic)

  (*let parse_file entry fname =
    let ic = open_in fname in
    let lb = Utf8.from_channel ic in
    set_filename lb fname; (* useful? *)
    let x = parse_lexbuf entry lb in
    close_in ic;
    x*)

  let parse_file (entry: lexbuf -> 'a) (fname: string): 'a Stream.t =
    parse_in_channel entry fname (open_in fname)

  (* exported functions *)
  let parse_search_query_string (fname: string) (s: string): query =
    Stream.next (parse_string (Ll1.alone Ll1.search) fname s)

  let parse_string = parse_string Ll1.command
  let parse_in_channel = parse_in_channel Ll1.command
  let parse_file = parse_file Ll1.command

end

include Lp

open Error

(** [path_of_string s] converts the string [s] into a path. *)
let path_of_string : string -> Path.t = fun s ->
  let lb = Utf8.from_string s in
  try
    begin match token lb () with
      | UID s, _, _ -> [s]
      | QID p, _, _ -> List.rev p
      | _ -> fatal_no_pos "Syntax error: \"%s\" is not a path." s
    end
  with SyntaxError _ ->
    fatal_no_pos "Syntax error: \"%s\" is not a path." s

(** [qident_of_string s] converts the string [s] into a qident. *)
let qident_of_string : string -> Core.Term.qident = fun s ->
  let lb = Utf8.from_string s in
  try
    begin match token lb () with
      | QID [], _, _ -> assert false
      | QID (s::p), _, _ -> (List.rev p, s)
      | _ ->
          fatal_no_pos "Syntax error: \"%s\" is not a qualified identifier." s
    end
  with SyntaxError _ ->
    fatal_no_pos "Syntax error: \"%s\" is not a qualified identifier." s

(** [parse_file fname] selects and runs the correct parser on file [fname], by
    looking at its extension. *)
let parse_file : string -> ast = fun fname ->
  match Filename.check_suffix fname Library.lp_src_extension with
  | true  -> Lp.parse_file fname
  | false -> Dk.parse_file fname
