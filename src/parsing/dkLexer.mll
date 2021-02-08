{
open Lexing
open Common
open Console
open Pos

let filename = ref ""

let make_pos : Lexing.position * Lexing.position -> 'a -> 'a loc =
  fun lps elt ->
    let fname = !filename in
    make (Some (locate ~fname lps)) elt

let locate_lexbuf : Lexing.lexbuf -> Pos.pos = fun lexbuf ->
  locate (lexbuf.lex_start_p, lexbuf.lex_curr_p)

type token =
  (* End of file. *)
  | EOF
  (* Keywords. *)
  | ASSERT of bool
  | EVAL
  | KW_DEF
  | KW_INJ
  | KW_PRV
  | KW_THM
  | INFER
  | REQUIRE of Module.Path.t
  | TYPE
  (* Symbols. *)
  | ARROW
  | COLON
  | COMMA
  | EQUAL
  | DEF
  | DOT
  | FATARROW
  | LEFTSQU
  | LEFTPAR
  | LONGARROW
  | RIGHTSQU
  | RIGHTPAR
  | UNDERSCORE
  (* Identifiers. *)
  | ID of string
  | QID of (string list * string)

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
  | eof                             { EOF                                  }
  | space                           { token lexbuf                         }
  | '\n'                            { new_line lexbuf; token lexbuf        }
  | "(;"                            { start_comment lexbuf; comment lexbuf }
  (* keywords *)
  | "#ASSERT"                       { ASSERT(false)                        }
  | "#ASSERTNOT"                    { ASSERT(true)                         }
  | "#EVAL"                         { EVAL                                 }
  | "def"                           { KW_DEF                               }
  | "inj"                           { KW_INJ                               }
  | "prv"                           { KW_PRV                               }
  | "thm"                           { KW_THM                               }
  | "#INFER"                        { INFER                                }
  | "#REQUIRE" space+ (mpath as mp) { REQUIRE(String.split_on_char '.' mp) }
  | "Type"                          { TYPE                                 }
  (* symbols *)
  | "->"                            { ARROW                                }
  | ','                             { COMMA                                }
  | ':'                             { COLON                                }
  | ":="                            { DEF                                  }
  | "=="                            { EQUAL                                }
  | '.'                             { DOT                                  }
  | "=>"                            { FATARROW                             }
  | '['                             { LEFTSQU                              }
  | '('                             { LEFTPAR                              }
  | "-->"                           { LONGARROW                            }
  | ']'                             { RIGHTSQU                             }
  | ')'                             { RIGHTPAR                             }
  | "_"                             { UNDERSCORE                           }
  (* identifiers *)
  | (mpath as mp) "." (ident as id) { QID(String.split_on_char '.' mp, id) }
  | ident  as x                     { ID(x)                                }
  | _ as c                          { unexpected_char lexbuf c             }

and comment = parse
  | "(;" { push_comment lexbuf; comment lexbuf                     }
  | ";)" { if pop_comment () then token lexbuf else comment lexbuf }
  | '\n' { new_line lexbuf; comment lexbuf                         }
  | _    { comment lexbuf                                          }
  | eof  { unclosed_comment ()                                     }
