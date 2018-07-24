let parse_channel ic =
  let lines = ref [] in
  let lexbuf = Lexing.from_channel ic in
  try
    while true do
      let l = Menhir_parser.line Lexer.token lexbuf in
      lines := l :: !lines
    done;
    assert false (* Unreachable. *)
  with
  | End_of_file         -> List.rev !lines
  | Menhir_parser.Error ->
      let lex = Lexing.lexeme lexbuf in
      Printf.printf "ERROR: unexpected token '%s'...\n%!" lex;
      assert false

let _ =
  let files = List.tl (Array.to_list Sys.argv) in
  let run_file fn =
    let ic = open_in fn in
    try
      let res = parse_channel ic in
      close_in ic;
      Printf.printf "\027[32mOK\027[0m on file %s (%i items).\n%!"
        fn (List.length res)
    with _ ->
      Printf.printf "\027[31mKO\027[0m on file %s\n%!" fn;
      close_in ic
  in
  List.iter run_file files
