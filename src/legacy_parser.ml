open Console

let parse_lexbuf : string -> Lexing.lexbuf -> Syntax.ast = fun fname lexbuf ->
  Pervasives.(Legacy_lexer.filename := fname);
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
      let loc = Some(Legacy_lexer.locate loc loc) in
      fatal loc "Unexpected token [%s]." (Lexing.lexeme lexbuf)

let parse_file : string -> Syntax.ast = fun fname ->
  let ic = open_in fname in
  let lexbuf = Lexing.from_channel ic in
  try let l = parse_lexbuf fname lexbuf in close_in ic; l
  with e -> close_in ic; raise e

let parse_string : string -> string -> Syntax.ast = fun fname s ->
  parse_lexbuf fname (Lexing.from_string s)
