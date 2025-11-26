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

  type lexbuf

  val parse_in_channel : string -> in_channel -> ast
  (** [parse f ic] returns a stream of commands parsed from channel [ic]
      created from file [f]. Commands are parsed lazily and the channel is
      closed once all entries are parsed. *)

  val parse_file : string -> ast
  (** [parse_file f] returns a stream of parsed commands of file [f]. Commands
      are parsed lazily. *)

  val parse_string : string -> string -> ast
  (** [parse_string f s] returns a stream of parsed commands from string [s]
      which comes from file [f] ([f] can be anything). *)

  val parse_lexbuf : lexbuf -> ast
  (** [parse_lexbuf lb] is the same as [parse_string] but with an already
      created lexbuf. *)

end

(* defined in OCaml >= 4.11 only *)
let set_filename (lb:lexbuf) (fname:string): unit =
  lb.lex_curr_p <- {lb.lex_curr_p with pos_fname = fname}

(** Parsing dk syntax. *)
module Dk : PARSER with type lexbuf := Lexing.lexbuf = struct

  open Lexing

  let parse_lexbuf (icopt:in_channel option)
        (entry:lexbuf -> 'a) (lb:lexbuf) : 'a Stream.t =
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
    let lb = from_channel ic in
    set_filename lb fname;
    parse_lexbuf (Some ic) entry lb

  let parse_file entry fname = parse_in_channel entry fname (open_in fname)

  let parse_string (entry: lexbuf -> 'a) (fname:string) (s:string)
      : 'a Stream.t =
    let lb = from_string s in
    set_filename lb fname;
    parse_lexbuf None entry lb

  let command =
    let r = ref (Pos.none (P_open(false,[]))) in
    fun (lb:lexbuf): p_command ->
    Debug.(record_time Parsing
             (fun () -> r := DkParser.line DkLexer.token lb)); !r

  (* exported functions *)
  let parse_string = parse_string command
  let parse_in_channel = parse_in_channel command
  let parse_file = parse_file command
  let parse_lexbuf = parse_lexbuf None command
end

open LpLexer
open Sedlexing

(** Parsing lp syntax. *)
module Lp :
sig
  include PARSER with type lexbuf := Sedlexing.lexbuf

  val parse_term_string: Lexing.position -> string -> Syntax.p_term
  (** [parse_rwpatt_string p s] parses a term from string [s] assuming that
      [s] starts at position [p]. *)

  val parse_rwpatt_string: Lexing.position -> string -> Syntax.p_rw_patt
  (** [parse_rwpatt_string f s] parses a rewrite pattern specification from
      string [s] assuming that [s] starts at position [p]. *)

  val parse_search_query_string: Lexing.position -> string -> Syntax.query
  (** [parse_search_query_string f s] parses a query from string [s] assuming
      that [s] starts at position [p]. *)

  end
= struct

  let handle_error (icopt: in_channel option)
        (entry: lexbuf -> 'a) (lb: lexbuf): 'a option =
    try Some(entry lb)
    with
    | End_of_file -> Option.iter close_in icopt; None
    | SyntaxError{pos=None; _} -> assert false
    | SyntaxError{pos=Some pos; elt} ->
        parser_fatal pos "Syntax error. %s" elt

  let parse_lexbuf (icopt: in_channel option)
        (entry: lexbuf -> 'a) (lb: lexbuf): 'a Stream.t =
    Stream.from (fun _ -> handle_error icopt entry lb)

  let parse_string (entry: lexbuf -> 'a) (fname: string) (s: string)
      : 'a Stream.t =
    let lb = Utf8.from_string s in
    set_filename lb fname;
    parse_lexbuf None entry lb

  let parse_in_channel (entry: lexbuf -> 'a) (fname:string) (ic: in_channel)
      : 'a Stream.t =
    let lb = Utf8.from_channel ic in
    set_filename lb fname;
    parse_lexbuf (Some ic) entry lb

  let parse_file (entry: lexbuf -> 'a) (fname: string): 'a Stream.t =
    parse_in_channel entry fname (open_in fname)

  let parse_entry_string (entry:lexbuf -> 'a) (lexpos:Lexing.position)
        (s:string): 'a =
    let lb = Utf8.from_string s in
    set_position lb lexpos;
    set_filename lb lexpos.pos_fname;
    Stream.next (parse_lexbuf None (LpParser.new_parsing entry) lb)

  (* exported functions *)
  let parse_term_string = parse_entry_string LpParser.term
  let parse_rwpatt_string = parse_entry_string LpParser.rw_patt_spec
  let parse_search_query_string = parse_entry_string LpParser.search

  let parse_in_channel = parse_in_channel LpParser.command
  let parse_file = parse_file LpParser.command
  let parse_string = parse_string LpParser.command
  let parse_lexbuf = parse_lexbuf None LpParser.command

end

include Lp

open Error

(** [path_of_string s] converts the string [s] into a path. *)
let path_of_string : string -> Path.t = fun s ->
  let lb = Utf8.from_string s in
  try
    begin match token lb with
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
    begin match token lb with
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
