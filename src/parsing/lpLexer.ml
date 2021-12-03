(** Lexer for Lambdapi syntax. Uses Sedlex, a Utf8 friendly lexer. Some helper
    functions to check if a string conflicts with the syntax are also
    provided. *)
open Lplib
open Sedlexing
open Common
open Pos

exception SyntaxError of strloc

let fail : Sedlexing.lexbuf -> string -> 'a = fun lb msg ->
  raise (SyntaxError (make_pos (lexing_positions lb) msg))

let invalid_character : Sedlexing.lexbuf -> 'a = fun lb ->
  fail lb ("Invalid character: \"" ^ Utf8.lexeme lb ^ "\".")

(** Tokens. *)
type token =
  (* end of file *)
  | EOF

  (* keywords in alphabetical order *)
  | ABORT
  | ADMIT
  | ADMITTED
  | APPLY
  | AS
  | ASSERT
  | ASSERTNOT
  | ASSOCIATIVE
  | ASSUME
  | BEGIN
  | BUILTIN
  | COMMUTATIVE
  | COMPUTE
  | CONSTANT
  | DEBUG
  | END
  | FAIL
  | FLAG
  | FOCUS
  | GENERALIZE
  | HAVE
  | IN
  | INDUCTION
  | INDUCTIVE
  | INFIX
  | INJECTIVE
  | LET
  | NOTATION
  | OPAQUE
  | OPEN
  | PREFIX
  | PRINT
  | PRIVATE
  | PROOFTERM
  | PROTECTED
  | PROVER
  | PROVER_TIMEOUT
  | QUANTIFIER
  | REFINE
  | REFLEXIVITY
  | REQUIRE
  | REWRITE
  | RULE
  | SEQUENTIAL
  | SIMPLIFY
  | SOLVE
  | SYMBOL
  | SYMMETRY
  | TYPE_QUERY
  | TYPE_TERM
  | UNIF_RULE
  | VERBOSE
  | WHY3
  | WITH

  (* other tokens *)
  | ASSOC of Pratter.associativity
  | DEBUG_FLAGS of (bool * string)
      (* Tuple constructor (with parens) required by Menhir. *)
  | INT of int
  | FLOAT of float
  | STRINGLIT of string
  | SWITCH of bool

  (* symbols *)
  | ARROW
  | ASSIGN
  | AT
  | BACKQUOTE
  | COMMA
  | COLON
  | DOLLAR
  | EQUIV
  | HOOK_ARROW
  | LAMBDA
  | L_CU_BRACKET
  | L_PAREN
  | L_SQ_BRACKET
  | PI
  | QUESTION_MARK
  | R_CU_BRACKET
  | R_PAREN
  | R_SQ_BRACKET
  | SEMICOLON
  | TURNSTILE
  | UNDERSCORE
  | VBAR

  (* identifiers *)
  | ID of string
  | PATH of Path.t (* in reverse order *)

(** Some regexp definitions. *)
let digit = [%sedlex.regexp? '0' .. '9']
let nonzero_nat = [%sedlex.regexp? '1' .. '9', Star digit]
let nat = [%sedlex.regexp? '0' | nonzero_nat]
let float = [%sedlex.regexp? nat, '.', Plus digit]
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
let forbidden_letter = [%sedlex.regexp? Chars " ,;\r\t\n(){}[]:.`\"@$|?"]
let regid = [%sedlex.regexp? Plus (Compl forbidden_letter)]

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
let escape s = if is_regid s then s else "{|" ^ s ^ "|}"

(** [remove_useless_escape s] replaces escaped regular identifiers by their
   unescape form. *)
let remove_useless_escape : string -> string = fun s ->
  let s' = Escape.unescape s in if is_regid s' then s' else s

let remove_first : Sedlexing.lexbuf -> string = fun lb ->
  Utf8.sub_lexeme lb 1 (lexeme_length lb - 1)

let remove_last : Sedlexing.lexbuf -> string = fun lb ->
  Utf8.sub_lexeme lb 0 (lexeme_length lb - 1)

(** Lexer. *)
let rec token lb =
  match%sedlex lb with

  (* end of file *)
  | eof -> EOF

  (* spaces *)
  | ' ' -> token lb
  | '\t' -> token lb
  | '\n' -> token lb
  | '\r' -> token lb

  (* comments *)
  | oneline_comment -> token lb
  | "/*" -> comment 0 lb

  (* keywords *)
  | "abort" -> ABORT
  | "admit" -> ADMIT
  | "admitted" -> ADMITTED
  | "apply" -> APPLY
  | "as" -> AS
  | "assert" -> ASSERT
  | "assertnot" -> ASSERTNOT
  | "associative" -> ASSOCIATIVE
  | "assume" -> ASSUME
  | "begin" -> BEGIN
  | "builtin" -> BUILTIN
  | "commutative" -> COMMUTATIVE
  | "compute" -> COMPUTE
  | "constant" -> CONSTANT
  | "debug" -> DEBUG
  | "end" -> END
  | "fail" -> FAIL
  | "flag" -> FLAG
  | "focus" -> FOCUS
  | "generalize" -> GENERALIZE
  | "have" -> HAVE
  | "in" -> IN
  | "induction" -> INDUCTION
  | "inductive" -> INDUCTIVE
  | "infix" -> INFIX
  | "injective" -> INJECTIVE
  | "left" -> ASSOC(Pratter.Left)
  | "let" -> LET
  | "notation" -> NOTATION
  | "off" -> SWITCH(false)
  | "on" -> SWITCH(true)
  | "opaque" -> OPAQUE
  | "open" -> OPEN
  | "prefix" -> PREFIX
  | "print" -> PRINT
  | "private" -> PRIVATE
  | "proofterm" -> PROOFTERM
  | "protected" -> PROTECTED
  | "prover" -> PROVER
  | "prover_timeout" -> PROVER_TIMEOUT
  | "quantifier" -> QUANTIFIER
  | "refine" -> REFINE
  | "reflexivity" -> REFLEXIVITY
  | "require" -> REQUIRE
  | "rewrite" -> REWRITE
  | "right" -> ASSOC(Pratter.Right)
  | "rule" -> RULE
  | "sequential" -> SEQUENTIAL
  | "simplify" -> SIMPLIFY
  | "solve" -> SOLVE
  | "symbol" -> SYMBOL
  | "symmetry" -> SYMMETRY
  | "type" -> TYPE_QUERY
  | "TYPE" -> TYPE_TERM
  | "unif_rule" -> UNIF_RULE
  | "verbose" -> VERBOSE
  | "why3" -> WHY3
  | "with" -> WITH

  (* other tokens *)
  | '+', Plus lowercase -> DEBUG_FLAGS(true, remove_first lb)
  | '-', Plus lowercase -> DEBUG_FLAGS(false, remove_first lb)
  | nat -> INT(int_of_string (Utf8.lexeme lb))
  | float -> FLOAT(float_of_string (Utf8.lexeme lb))
  | string -> STRINGLIT(Utf8.sub_lexeme lb 1 (lexeme_length lb - 2))

  (* symbols *)
  | 0x2254 (* ≔ *) -> ASSIGN
  | 0x2192 (* → *) -> ARROW
  | '`' -> BACKQUOTE
  | ',' -> COMMA
  | ':' -> COLON
  | 0x2261 (* ≡ *) -> EQUIV
  | 0x21aa (* ↪ *) -> HOOK_ARROW
  | 0x03bb (* λ *) -> LAMBDA
  | '{' -> L_CU_BRACKET
  | '(' -> L_PAREN
  | '[' -> L_SQ_BRACKET
  | 0x03a0 (* Π *) -> PI
  | '}' -> R_CU_BRACKET
  | ')' -> R_PAREN
  | ']' -> R_SQ_BRACKET
  | ';' -> SEMICOLON
  | 0x22a2 (* ⊢ *) -> TURNSTILE
  | '|' -> VBAR
  | '_' -> UNDERSCORE
  | '?' -> QUESTION_MARK
  | '$' -> DOLLAR
  | '@' -> AT

  (* identifiers *)
  | regid -> ID(Utf8.lexeme lb)
  | escid -> ID(remove_useless_escape(Utf8.lexeme lb))

  | regid, '.' -> path [remove_last lb] lb
  | escid, '.' -> path [remove_useless_escape(remove_last lb)] lb

  (* invalid character *)
  | _ -> invalid_character lb

and path ids lb =
  match%sedlex lb with
  | regid, '.' -> path (remove_last lb :: ids) lb
  | escid, '.' -> path (remove_useless_escape(remove_last lb) :: ids) lb
  | regid -> PATH(Utf8.lexeme lb :: ids)
  | escid -> PATH(remove_useless_escape (Utf8.lexeme lb) :: ids)
  | _ ->
    fail lb ("Invalid identifier: \""
             ^ String.concat "." (List.rev (Utf8.lexeme lb :: ids)) ^ "\".")

and comment i lb =
  match%sedlex lb with
  | eof -> fail lb "Unterminated comment."
  | "*/" -> if i=0 then token lb else comment (i-1) lb
  | "/*" -> comment (i+1) lb
  | any -> comment i lb
  | _ -> invalid_character lb

(** [token buf] is a lexing function on buffer [buf] that can be passed to
    a parser. *)
let token : lexbuf -> unit -> token * Lexing.position * Lexing.position =
  with_tokenizer token

let token =
  let r = ref (EOF, Lexing.dummy_pos, Lexing.dummy_pos) in fun lb () ->
  Debug.(record_time Lexing (fun () -> r := token lb ())); !r
