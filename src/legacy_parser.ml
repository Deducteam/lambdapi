open Console

let parse_channel : in_channel -> Parser.p_cmd Pos.loc list = fun ic ->
  let lines = ref [] in
  let lexbuf = Lexing.from_channel ic in
  try
    while true do
      let l = Menhir_parser.line Legacy_lexer.token lexbuf in
      lines := l :: !lines
    done;
    assert false (* Unreachable. *)
  with
  | End_of_file         -> List.rev !lines
  | Menhir_parser.Error ->
      let lex = Lexing.lexeme lexbuf in
      fatal_no_pos "ERROR: unexpected token '%s'...\n%!" lex

let parse_file : string -> Parser.p_cmd Pos.loc list = fun fname ->
  let ic = open_in fname in
  try
    let l = parse_channel ic in
    close_in ic; l
  with e ->
    close_in ic; raise e
