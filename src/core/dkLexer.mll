{
open Console
open Lexing
open Pos

let filename = Stdlib.ref ""

let to_module_path : string -> Syntax.p_module_path = fun mp ->
  List.map (fun s -> (s, false)) (String.split_on_char '.' mp)

let make_pos : Lexing.position * Lexing.position -> 'a -> 'a loc =
  fun lps elt -> {pos = Some(locate lps); elt}

let locate_lexbuf : Lexing.lexbuf -> Pos.pos = fun lexbuf ->
  locate (lexbuf.lex_start_p, lexbuf.lex_curr_p)

type token =
  (* Special characters and symbols. *)
  | L_SQB | R_SQB | L_PAR | R_PAR | ARROW | LARROW | FARROW | DEFEQ | COMMA
  | COLON | EQUAL | DOT | EOF
  (* Keywords. *)
  | KW_DEF | KW_INJ | KW_THM | TYPE | KW_PRV | KW_SEQ
  (* Identifiers and wildcard. *)
  | WILD
  | ID      of string
  | QID     of (Syntax.p_module_path * string)
  (* Commands. *)
  | REQUIRE of Syntax.p_module_path
  | EVAL
  | INFER
  | ASSERT  of bool

let unexpected_char : Lexing.lexbuf -> char -> token = fun lexbuf c ->
  fatal (Some(locate_lexbuf lexbuf)) "Unexpected characters [%c]." c

let comment_stack = Stack.create ()

let start_comment lexbuf =
  Stack.clear comment_stack;
  Stack.push (locate_lexbuf lexbuf) comment_stack

let push_comment lexbuf =
  Stack.push (locate_lexbuf lexbuf) comment_stack

let pop_comment () =
  ignore (try Stack.pop comment_stack with Stack.Empty -> assert false);
  Stack.is_empty comment_stack

let unclosed_comment () =
  let loc = try Stack.pop comment_stack with Stack.Empty -> assert false in
  fatal (Some(loc)) "Unclosed comment."
}

let space  = [' ''\t''\r']
let mident = ['a'-'z''A'-'Z''0'-'9''_']+
let mpath  = (mident ".")* mident
let ident  =
  ['a'-'z''A'-'Z''0'-'9''_''!''?']['a'-'z''A'-'Z''0'-'9''_''!''?''\'']*

rule token = parse
  | space                           { token lexbuf                         }
  | '\n'                            { new_line lexbuf; token lexbuf        }
  | "(;"                            { start_comment lexbuf; comment lexbuf }
  | '.'                             { DOT                                  }
  | ','                             { COMMA                                }
  | ':'                             { COLON                                }
  | "=="                            { EQUAL                                }
  | '['                             { L_SQB                                }
  | ']'                             { R_SQB                                }
  | '('                             { L_PAR                                }
  | ')'                             { R_PAR                                }
  | "-->"                           { LARROW                               }
  | "->"                            { ARROW                                }
  | "=>"                            { FARROW                               }
  | ":="                            { DEFEQ                                }
  | "_"                             { WILD                                 }
  | "Type"                          { TYPE                                 }
  | "def"                           { KW_DEF                               }
  | "inj"                           { KW_INJ                               }
  | "thm"                           { KW_THM                               }
  | "prv"                           { KW_PRV                               }
  | "#REQUIRE" space+ (mpath as mp) { REQUIRE(to_module_path mp)           }
  | "#EVAL"                         { EVAL                                 }
  | "#INFER"                        { INFER                                }
  | "#ASSERT"                       { ASSERT(false)                        }
  | "#ASSERTNOT"                    { ASSERT(true)                         }
  | (mpath as mp) "." (ident as id) { QID(to_module_path mp, id)           }
  | ident  as x                     { ID(x)                                }
  | _ as c                          { unexpected_char lexbuf c             }
  | eof                             { EOF                                  }

and comment = parse
  | "(;" { push_comment lexbuf; comment lexbuf                     }
  | ";)" { if pop_comment () then token lexbuf else comment lexbuf }
  | '\n' { new_line lexbuf; comment lexbuf                         }
  | _    { comment lexbuf                                          }
  | eof  { unclosed_comment ()                                     }
