(** Dedukti source file parsing/tokens.ml. *)

open DkBasic

type loc = Lexing.position * Lexing.position

type token =
  | UNDERSCORE of loc
  | TYPE of loc
  | KW_DEF of loc
  | KW_DEFAC of loc
  | KW_DEFACU of loc
  | KW_THM of loc
  | KW_INJ of loc
  | KW_PRV of loc
  | RIGHTSQU
  | RIGHTPAR
  | RIGHTBRA
  | QID of (loc * mident * ident)
  | NAME of (loc * mident)
  | REQUIRE of (loc * mident)
  | TYPE_CLASS of (loc * ident)
  | TYPE_CLASS_INSTANCE of (loc * ident)
  | LONGARROW
  | LEFTSQU
  | LEFTPAR
  | LEFTBRA
  | ID of (loc * ident)
  | FATARROW
  | EOF
  | DOT
  | DEF
  | COMMA
  | COLON
  | EQUAL
  | ARROW
  | EVAL of loc
  | INFER of loc
  | CHECK of loc
  | ASSERT of loc
  | CHECKNOT of loc
  | ASSERTNOT of loc
  | PRINT of loc
  | GDT of loc
  | STRING of string
