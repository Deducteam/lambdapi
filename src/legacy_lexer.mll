{
open Lexing
open Pos

let locate : Lexing.position -> Lexing.position -> Pos.pos = fun p1 p2 ->
  let fname = if p1.pos_fname = "" then None else Some(p1.pos_fname) in
  let start_line = p1.pos_lnum in
  let start_col = p1.pos_cnum - p1.pos_bol in
  let end_line = p2.pos_lnum in
  let end_col = p2.pos_cnum - p2.pos_bol in
  Lazy.from_val {fname; start_line; start_col; end_line; end_col}

let make_pos : Lexing.position * Lexing.position -> 'a -> 'a Pos.loc =
  fun (p1,p2) elt -> {pos = Some(locate p1 p2); elt}

type token =
  | UNDERSCORE
  | TYPE
  | KW_DEF
  | KW_INJ
  | KW_THM
  | RIGHTSQU
  | RIGHTPAR
  | RIGHTBRA
  | QID        of (string * string)
  | REQUIRE    of string
  | LONGARROW
  | LEFTSQU
  | LEFTPAR
  | LEFTBRA
  | ID         of string
  | FATARROW
  | EOF
  | DOT
  | DEF
  | COMMA
  | COLON
  | CCOLON
  | EQUAL
  | ARROW
  | EVAL
  | INFER
  | ASSERT     of bool
  | PRINT
  | GDT
  | INT        of int
}

let space   = [' ''\t''\r']
let mident  = ['a'-'z''A'-'Z''0'-'9''_']+
let ident   =
  ['a'-'z''A'-'Z''0'-'9''_''!' '?']['a'-'z''A'-'Z''0'-'9''_''!''?''\'']*
let capital = ['A'-'Z']+

rule token = parse
  | space       { token lexbuf  }
  | '\n'        { new_line lexbuf ; token lexbuf }
  | "(;"        { comment lexbuf}
  | '.'         { DOT           }
  | ','         { COMMA         }
  | ':'         { COLON         }
  | "=="        { EQUAL         }
  | '['         { LEFTSQU       }
  | ']'         { RIGHTSQU      }
  | '{'         { LEFTBRA       }
  | '}'         { RIGHTBRA      }
  | '('         { LEFTPAR       }
  | ')'         { RIGHTPAR      }
  | "-->"       { LONGARROW     }
  | "->"        { ARROW         }
  | "=>"        { FATARROW      }
  | ":="        { DEF           }
  | "_"         { UNDERSCORE    }
  | "Type"      { TYPE          }
  | "def"       { KW_DEF        }
  | "inj"       { KW_INJ        }
  | "thm"       { KW_THM        }
  | "#REQUIRE" space+ (mident as md) { REQUIRE md }
  | "#EVAL"     { EVAL          }
  | "#INFER"    { INFER         }
  | "#ASSERT"   { ASSERT(false) }
  | "#ASSERTNOT"{ ASSERT(true)  }
  | "#PRINT"    { PRINT         }
  | "#GDT"      { GDT           }
  | mident as md '.' (ident as id) { QID (md, id) }
  | ident  as id { ID  id }
  | _   as c    { failwith (Printf.sprintf "Unexpected characters '%c'." c) }
  | eof         { EOF }

and comment = parse
  | ";)" { token lexbuf }
  | '\n' { new_line lexbuf ; comment lexbuf }
  | _    { comment lexbuf }
  | eof  { failwith "Unclosed comment." }
