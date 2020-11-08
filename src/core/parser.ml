(** Parsing functions for the Lambdapi syntax based on the Earley library. See
    https://github.com/rlepigre/ocaml-earley/blob/master/README.md for details
    on using the library and its syntax extension. *)

open! Lplib

open Syntax
open Pos
open Parser_utils

(* TODO: move to right place *)
type prio = PFunc | PAtom | PAppl

(** [add_prefix p s] adds the prefix [p] at the beginning of the
    identifier [s]. *)
let add_prefix : string -> string -> string = fun p s ->
  let n = String.length s in
  if n >= 4 && s.[0] ='{' && s.[1] = '|' then
    "{|" ^ p ^ String.sub s 2 (n-4) ^ "|}"
  else
    p ^ s

let parse_file : string -> Syntax.ast = fun fname ->
  let inchan = open_in fname in
  let parse =
    MenhirLib.Convert.Simplified.traditional2revised Lp_parser.command
  in
  let lexbuf = Sedlexing.Utf8.from_channel inchan in
  Sedlexing.set_filename lexbuf fname;
  let lexer = Lp_lexer.lexer lexbuf in
  let cmds = ref [] in
  let res =
    try
      while true do
        let cmd = parse lexer in
        cmds := cmd :: !cmds;
      done;
      assert false (* Should raise end of file before *)
    with
    | End_of_file -> List.rev !cmds
    | Lp_lexer.SyntaxError(s) ->
        let loc = match s.pos with Some(l) -> l | None -> assert false in
        parser_fatal loc "Unexpected character: [%s]" s.elt
    | Lp_parser.Error ->
        let loc = Sedlexing.lexing_positions lexbuf in
        let loc = Pos.locate loc in
        parser_fatal loc "Unexpected token [%s]."
          (Sedlexing.Utf8.lexeme lexbuf)
  in
  close_in inchan;
  res

let parse_string : string -> string -> Syntax.ast = fun _ _ -> assert false

let parse_qident : string -> (qident, pos) result = fun _ -> assert false

let do_require : _ -> _ -> unit = fun _ _ -> assert false

module Legacy = struct
  (** Interface for the legacy parser. *)

  (** {b NOTE} we maintain the invariant described in the [Parser] module:
      every error should have an attached position. We do not open [Console]
      to avoid calls to [Console.fatal] and [Console.fatal_no_pos]. In case of
      an error, the [parser_fatal] function should be used instead. *)

  let parse_lexbuf : string -> Lexing.lexbuf -> Syntax.ast =
    fun fname lexbuf ->
    Stdlib.(Legacy_lexer.filename := fname);
    let lines = ref [] in
    try
      while true do
        let l = Menhir_parser.line Legacy_lexer.token lexbuf in
        lines := l :: !lines
      done;
      assert false (* Unreachable. *)
    with
    | End_of_file         -> List.rev !lines
    | Menhir_parser.Error ->
        let loc = Lexing.(lexbuf.lex_start_p) in
        let loc = Legacy_lexer.locate (loc, loc) in
        parser_fatal loc "Unexpected token [%s]." (Lexing.lexeme lexbuf)

  let parse_file : string -> Syntax.ast = fun fname ->
    let ic = open_in fname in
    let lexbuf = Lexing.from_channel ic in
    try let l = parse_lexbuf fname lexbuf in close_in ic; l
    with e -> close_in ic; raise e

  let parse_string : string -> string -> Syntax.ast = fun fname s ->
    parse_lexbuf fname (Lexing.from_string s)
end
