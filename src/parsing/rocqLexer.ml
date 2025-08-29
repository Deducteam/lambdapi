(** Lexer for Rocq syntax, using Sedlex, a Utf8 lexer generator. *)

open Lplib
open Sedlexing
open Common open Pos

let remove_first : Sedlexing.lexbuf -> string = fun lb ->
  Utf8.sub_lexeme lb 1 (lexeme_length lb - 1)

let remove_last : Sedlexing.lexbuf -> string = fun lb ->
  Utf8.sub_lexeme lb 0 (lexeme_length lb - 1)

let remove_ends : Sedlexing.lexbuf -> string = fun lb ->
  Utf8.sub_lexeme lb 1 (lexeme_length lb - 2)

exception SyntaxError of strloc

let syntax_error : Lexing.position * Lexing.position -> string -> 'a =
  fun pos msg -> raise (SyntaxError (Pos.make_pos pos msg))

let fail : Sedlexing.lexbuf -> string -> 'a = fun lb msg ->
  syntax_error (Sedlexing.lexing_positions lb) msg

let invalid_character : Sedlexing.lexbuf -> 'a = fun lb ->
  fail lb "Invalid character"

(** Tokens. *)
type token =
  (* end of file *)
  | EOF

  (* keywords in alphabetical order *)
  | GENERALIZE
  | IN
  | LET
  | RULE
  | TYPE_QUERY
  | TYPE_TERM

  (* other tokens *)
  | INT of string
  | STRINGLIT of string

  (* symbols *)
  | ARROW
  | ASSIGN
  | BACKQUOTE
  | COMMA
  | COLON
  | DOT
  | EXISTS
  | FORALL
  | FUN
  | LAMBDA
  | L_PAREN
  | L_SQ_BRACKET
  | PI
  | R_PAREN
  | R_SQ_BRACKET
  | SEMICOLON
  | THICKARROW
  | UNDERSCORE
  | VBAR

  (* identifiers *)
  | UID of string
  | UID_EXPL of string
  | UID_META of int
  | UID_PATT of string
  | QID of Path.t (* in reverse order *)
  | QID_EXPL of Path.t (* in reverse order *)

(** Some regexp definitions. *)
let space = [%sedlex.regexp? Chars " \t\n\r"]
let digit = [%sedlex.regexp? '0' .. '9']
let nat = [%sedlex.regexp? Plus digit]
let int = [%sedlex.regexp? nat | '-', nat]
let float = [%sedlex.regexp? int, '.', Plus digit]
let oneline_comment = [%sedlex.regexp? "//", Star (Compl ('\n' | '\r'))]
let string = [%sedlex.regexp? '"', Star (Compl '"'), '"']

(** Identifiers.

   There are two kinds of identifiers: regular identifiers and escaped
   identifiers of the form ["{|...|}"].

   Modulo those surrounding brackets, escaped identifiers allow to use as
   identifiers keywords or filenames that are not regular identifiers.

   An escaped identifier denoting a filename or directory is unescaped before
   accessing to it. Hence, the module ["{|a b|}"] refers to the file ["a b"].

   Identifiers need to be normalized so that an escaped identifier, once
   unescaped, is not regular. To this end, every identifier of the form
   ["{|s|}"] with s regular, is understood as ["s"] (function
   [remove_useless_escape] below).

   Finally, identifiers must not be empty, so that we can use the empty string
   for the path of ghost signatures. *)

(** Unqualified regular identifiers are any non-empty sequence of characters
   not among: *)
let forbidden_letter = [%sedlex.regexp? Chars " ,;\r\t\n(){}[]:.`\"@$|/"]
let regid = [%sedlex.regexp? '/' | Plus (Compl forbidden_letter)]

let is_regid : string -> bool = fun s ->
  let lb = Utf8.from_string s in
  match%sedlex lb with
  | regid, eof -> true
  | _ -> false

(** Unqualified escaped identifiers are any non-empty sequence of characters
    (except "|}") between "{|" and "|}". *)
let notbars = [%sedlex.regexp? Star (Compl '|')]
let escid = [%sedlex.regexp?
    "{|", notbars, '|', Star ('|' | Compl (Chars "|}"), notbars, '|'), '}']

(** [escape s] converts a string [s] into an escaped identifier if it is not
   regular. We do not check whether [s] contains ["|}"]. FIXME? *)
let escape s = if is_regid s then s else Escape.escape s

(** [remove_useless_escape s] replaces escaped regular identifiers by their
   unescape form. *)
let remove_useless_escape : string -> string = fun s ->
  let s' = Escape.unescape s in if is_regid s' then s' else s

(** Lexer. *)
let rec token lb =
  match%sedlex lb with

  (* end of file *)
  | eof -> EOF

  (* spaces *)
  | space -> token lb

  (* comments *)
  | oneline_comment -> token lb
  | "/*" -> comment token 0 lb

  (* keywords *)
  | "exists" -> EXISTS  (* in Coq *)
  | "forall" -> FORALL  (* in Coq *)
  | "fun" -> FUN  (* in Coq *)
  | "generalize" -> GENERALIZE
  | "in" -> IN
  | "let" -> LET
  | "rule" -> RULE
  | "type" -> TYPE_QUERY
  | "TYPE" -> TYPE_TERM

  (* other tokens *)
  | int -> INT(Utf8.lexeme lb)
  | string -> STRINGLIT(Utf8.sub_lexeme lb 1 (lexeme_length lb - 2))

  (* symbols *)
  | 0x2254 (* ≔ *) -> ASSIGN
  | 0x2192 (* → *) -> ARROW  (* not in Coq! *)
  | "->" -> ARROW  (* in Coq *)
  | "=>" -> THICKARROW  (* in Coq *)
  | '`' -> BACKQUOTE
  | ',' -> COMMA
  | ':' -> COLON
  | '.' -> DOT
  | 0x03bb (* λ *) -> LAMBDA  (* not in Coq! *)
  | '(' -> L_PAREN
  | '[' -> L_SQ_BRACKET
  | 0x03a0 (* Π *) -> PI
  | ')' -> R_PAREN
  | ']' -> R_SQ_BRACKET
  | ';' -> SEMICOLON
  | '|' -> VBAR
  | '_' -> UNDERSCORE

  (* rocq identifiers *)
  | "\\/" -> UID("∨")
  | "/\\" -> UID("∧")
  | "~" -> UID("¬")

  (* identifiers *)
  | regid -> UID(Utf8.lexeme lb)
  | escid -> UID(remove_useless_escape(Utf8.lexeme lb))
  | '@', regid -> UID_EXPL(remove_first lb)
  | '@', escid -> UID_EXPL(remove_useless_escape(remove_first lb))
  | '?', nat -> UID_META(int_of_string(remove_first lb))
  | '$', regid -> UID_PATT(remove_first lb)
  | '$', escid -> UID_PATT(remove_useless_escape(remove_first lb))
  | '$', nat -> UID_PATT(remove_first lb)

  | regid, '.' -> qid false [remove_last lb] lb
  | escid, '.' -> qid false [remove_useless_escape(remove_last lb)] lb
  | '@', regid, '.' -> qid true [remove_ends lb] lb
  | '@', escid, '.' -> qid true [remove_useless_escape(remove_ends lb)] lb

  (* invalid character *)
  | _ -> invalid_character lb

and qid expl ids lb =
  match%sedlex lb with
  | oneline_comment -> qid expl ids lb
  | "/*" -> comment (qid expl ids) 0 lb
  | regid, '.' -> qid expl (remove_last lb :: ids) lb
  | escid, '.' -> qid expl (remove_useless_escape(remove_last lb) :: ids) lb
  | regid ->
    if expl then QID_EXPL(Utf8.lexeme lb :: ids)
    else QID(Utf8.lexeme lb :: ids)
  | escid ->
    if expl then QID_EXPL(remove_useless_escape (Utf8.lexeme lb) :: ids)
    else QID(remove_useless_escape (Utf8.lexeme lb) :: ids)
  | _ ->
    fail lb ("Invalid identifier: \""
             ^ String.concat "." (List.rev (Utf8.lexeme lb :: ids)) ^ "\".")

and comment next i lb =
  match%sedlex lb with
  | eof -> fail lb "Unterminated comment."
  | "*/" -> if i=0 then next lb else comment next (i-1) lb
  | "/*" -> comment next (i+1) lb
  | any -> comment next i lb
  | _ -> invalid_character lb

(** [token buf] is a lexing function on buffer [buf] that can be passed to
    a parser. *)
let token : lexbuf -> unit -> token * Lexing.position * Lexing.position =
  fun lb () -> try with_tokenizer token lb () with
  | Sedlexing.MalFormed -> fail lb "Not Utf8 encoded file"
  | Sedlexing.InvalidCodepoint k ->
      fail lb ("Invalid Utf8 code point " ^ string_of_int k)

let token =
  let r = ref (EOF, Lexing.dummy_pos, Lexing.dummy_pos) in fun lb () ->
  Debug.(record_time Lexing (fun () -> r := token lb ())); !r
