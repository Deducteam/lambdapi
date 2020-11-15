(** Interface for the legacy parser. *)

(** {b NOTE} we maintain the invariant described in the [Parser] module: every
    error should have an attached position.  We do not open [Console] to avoid
    calls to [Console.fatal] and [Console.fatal_no_pos].  In case of an error,
    the [parser_fatal] function should be used instead. *)
type ast = P_term.p_term Syntax.ast

let parse_lexbuf : string -> Lexing.lexbuf -> ast = fun fname lexbuf ->
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
      Parser.parser_fatal loc "Unexpected token [%s]." (Lexing.lexeme lexbuf)

let parse_file : string -> ast = fun fname ->
  let ic = open_in fname in
  let lexbuf = Lexing.from_channel ic in
  try let l = parse_lexbuf fname lexbuf in close_in ic; l
  with e -> close_in ic; raise e

let parse_string : string -> string -> ast = fun fname s ->
  parse_lexbuf fname (Lexing.from_string s)
