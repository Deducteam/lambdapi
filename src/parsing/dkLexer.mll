{
  (** Dedukti source file parsing/lexer.mll. *)

  open DkBasic
  open Lexing
  open DkTokens
  open Format
  open Common

  let get_loc lexbuf = lexbuf.lex_start_p, lexbuf.lex_curr_p

  let fail lps msg = Error.fatal (Some (Pos.locate lps)) "%s" msg
}

let space   = [' ' '\t' '\r']
let mident = ['a'-'z' 'A'-'Z' '0'-'9' '_']+
let ident   = ['a'-'z' 'A'-'Z' '0'-'9' '_' '!' '?']['a'-'z' 'A'-'Z' '0'-'9' '_' '!' '?' '\'' ]*
let capital = ['A'-'Z']+

rule token = parse
  | space       { token lexbuf  }
  | '\n'        { new_line lexbuf ; token lexbuf }
  | "(;"        { comment 0 lexbuf}
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
  | "_"         { UNDERSCORE ( get_loc lexbuf ) }
  | "Type"      { TYPE       ( get_loc lexbuf ) }
  | "def"       { KW_DEF     ( get_loc lexbuf ) }
  | "defac"     { KW_DEFAC   ( get_loc lexbuf ) }
  | "defacu"    { KW_DEFACU  ( get_loc lexbuf ) }
  | "injective" { KW_INJ     ( get_loc lexbuf ) }
  | "thm"       { KW_THM     ( get_loc lexbuf ) }
  | "private"   { KW_PRV     ( get_loc lexbuf ) }
  | "#NAME"    space+ (mident as md) { NAME    (get_loc lexbuf , mk_mident md) }
  | "#REQUIRE" space+ (mident as md) { REQUIRE (get_loc lexbuf , mk_mident md) }
  | "#EVAL"     { EVAL       ( get_loc lexbuf ) }
  | "#INFER"    { INFER      ( get_loc lexbuf ) }
  | "#CHECK"    { CHECK      ( get_loc lexbuf ) }
  | "#CHECKNOT" { CHECKNOT   ( get_loc lexbuf ) }
  | "#ASSERT"   { ASSERT     ( get_loc lexbuf ) }
  | "#ASSERTNOT"{ ASSERTNOT  ( get_loc lexbuf ) }
  | "#PRINT"    { PRINT      ( get_loc lexbuf ) }
  | "#GDT"      { GDT        ( get_loc lexbuf ) }
  | mident as md '.' (ident as id)
  { QID ( get_loc lexbuf , mk_mident md , mk_ident id ) }
  | ident  as id
  { ID  ( get_loc lexbuf , mk_ident id ) }
  | '{' '|' { sident None (Buffer.create 42) lexbuf }
  | mident as md '.' '{' '|'
  {sident (Some (mk_mident md)) (Buffer.create 42) lexbuf}
  | '"' { string (Buffer.create 42) lexbuf }
  | _   as s
  { let msg = sprintf "Unexpected characters '%s'." (String.make 1 s) in
    fail (get_loc lexbuf) msg }
  | eof { EOF }

and comment i = parse
  | ";)" { if (i=0) then token lexbuf else comment (i-1) lexbuf }
  | '\n' { new_line lexbuf ; comment i lexbuf }
  | "(;" { comment (i+1) lexbuf }
  | _    { comment i lexbuf }
  | eof  { fail (get_loc lexbuf) "Unexpected end of file."  }

and string buf = parse
  | '\\' (_ as c)
  { Buffer.add_char buf '\\'; Buffer.add_char buf c; string buf lexbuf }
  | '\n'
  { Lexing.new_line lexbuf ; Buffer.add_char buf '\n'; string buf lexbuf }
  | '"'
  { STRING (Buffer.contents buf) }
  | _ as c
  { Buffer.add_char buf c; string buf lexbuf }
  | eof
  { fail (get_loc lexbuf) "Unexpected end of file in string." }

and sident op buf = parse
  | '\\' (_ as c)
  { Buffer.add_char buf '\\'; Buffer.add_char buf c; sident op buf lexbuf }
  | '|' '}'
  { match op with
    | None ->  ID  ( get_loc lexbuf , mk_ident ("{|" ^ (Buffer.contents buf) ^ "|}") )
    | Some md -> QID ( get_loc lexbuf , md, mk_ident ("{|" ^ (Buffer.contents buf) ^ "|}") )}
  | '\n'
  { fail (get_loc lexbuf) "Unexpected new line in ident." }
  | ' '
  { fail (get_loc lexbuf) "Unexpected space in ident." }
  | _ as c
  { Buffer.add_char buf c; sident op buf lexbuf }
  | eof
  { fail (get_loc lexbuf) "Unexpected end of file in ident." }

and is_ident = parse
  | ident { true }
  | _ { false }
