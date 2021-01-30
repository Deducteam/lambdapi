(** Lexer for Lambdapi syntax. Uses Sedlex, a Utf8 friendly lexer. Some helper
    functions to check if a string conflicts with the syntax are also
    provided. *)
open Lplib
open Sedlexing
open Pos

type token =
  (* end of file *)
  | EOF

  (* keywords in alphabetical order *)
  | ABORT
  | ADMIT
  | APPLY
  | AS
  | ASSERT
  | ASSERT_NOT
  | ASSUME
  | BEGIN
  | BUILTIN
  | COMPUTE
  | CONSTANT
  | DEBUG
  | END
  | FAIL
  | FLAG
  | FOCUS
  | IN
  | INDUCTIVE
  | INFIX
  | INJECTIVE
  | LET
  | OPEN
  | OPAQUE
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
  | SET
  | SIMPL
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
  | ASSIGN
  | ARROW
  | BACKQUOTE
  | COMMA
  | COLON
  | EQUIV
  | HOOK_ARROW
  | LAMBDA
  | L_CU_BRACKET
  | L_PAREN
  | L_SQ_BRACKET
  | PI
  | R_CU_BRACKET
  | R_PAREN
  | R_SQ_BRACKET
  | SEMICOLON
  | TURNSTILE
  | VBAR
  | WILD

  (* identifiers *)
  | ID of (string * bool) (* Boolean is true if the identifier is escaped. *)
  | ID_META of string
  | ID_PAT of string
  | QID of (string * bool) list
  | QID_EXPL of (string * bool) list

exception SyntaxError of strloc

(** Lexer for Lambdapi syntax. *)
module Lp_lexer : sig

  val is_identifier : string -> bool
  (** [is_identifier s] is [true] if [s] is a valid identifier. *)

  val is_keyword : string -> bool
  (** [is_keyword s] returns [true] if [s] is a keyword. *)

  val unquote : string -> string
  (** [unquote s] removes the quotation marks [{|] and [|}] from [s] if it has
      some. Otherwise, the argument is returned. *)

  val is_debug_flag : string -> bool
  (** [is_debug_flag s] is true if [s] is a debug flag. *)

  val lexer : lexbuf -> unit -> token * Lexing.position * Lexing.position
  (** [lexer buf] is a lexing function on buffer [buf] that can be passed to
      a parser. *)
end = struct
  let digit = [%sedlex.regexp? '0' .. '9']
  let integer = [%sedlex.regexp? Plus digit]

  (* We define the set of UTF8 codepoints that make up identifiers. The
     builtin categories are described on the home page of sedlex
     @see https://github.com/ocaml-community/sedlex *)

  let superscript =
    [%sedlex.regexp? 0x2070 | 0x00b9 | 0x00b2 | 0x00b3 | 0x2074 .. 0x207c]
  let subscript = [%sedlex.regexp? 0x208 .. 0x208c]
  let supplemental_punctuation = [%sedlex.regexp? 0x2e00 .. 0x2e52]
  let alphabet = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
  let ascii_sub =
    [%sedlex.regexp? '-' | '\'' | '&' | '^' | '\\' | '*'
                   | '%' | '#' | '~']
  let letter =
    [%sedlex.regexp? lowercase | uppercase | ascii_sub
                   | math | other_math | subscript | superscript
                   | supplemental_punctuation ]
  let id = [%sedlex.regexp? (letter | '_'), Star (letter | digit | '_')]
  let escid =
    [%sedlex.regexp? "{|", Star (Compl '|' | '|', Compl '}'), Star '|', "|}"]
  let path = [%sedlex.regexp? (id | escid), Plus ('.', (id | escid))]
  let stringlit = [%sedlex.regexp? '"', Star (Compl ('"' | '\n')), '"']
  let float = [%sedlex.regexp? integer, '.', Opt (integer)]
  let comment = [%sedlex.regexp? "//", Star (Compl ('\n' | '\r'))]

  (** [nom buf] eats whitespaces and comments in buffer [buf]. *)
  let rec nom : lexbuf -> unit = fun buf ->
    match%sedlex buf with
    | ' ' -> nom buf
    | '\t' -> nom buf
    | '\n' -> nom buf
    | '\r' -> nom buf
    | "\r\n" -> nom buf
    | "/*" -> nom_comment buf
    | comment -> nom buf
    | _ -> ()
and nom_comment : lexbuf -> unit = fun buf ->
    match%sedlex buf with
    | eof -> raise (SyntaxError (Pos.none "Unterminated comment."))
    | "*/" -> nom buf
    | any -> nom_comment buf
    | _ -> assert false

  (** [is_escaped s] is true if string [s] is escaped: i.e. enclosed in "{|
      |}". *)
  let is_escaped : string -> bool = fun s ->
    let buf = Utf8.from_string s in
    match%sedlex buf with
    | escid -> true
    | _ -> false

  let unquote : string -> string * bool = fun s ->
    if is_escaped s then String.(sub s 2 (length s - 4)), true else s, false

  (** [is_identifier s] is true if [s] is an identifier. *)
  let is_identifier : string -> bool = fun s ->
    let lexbuf = Sedlexing.Utf8.from_string s in
    match%sedlex lexbuf with
    | id -> true
    | _ -> false

  let is_keyword : string -> bool =
    let kws =
      List.sort String.compare
        [ "abort"
        ; "admit"
        ; "apply"
        ; "as"
        ; "assert"
        ; "assertnot"
        ; "assume"
        ; "begin"
        ; "builtin"
        ; "compute"
        ; "constant"
        ; "debug"
        ; "end"
        ; "fail"
        ; "flag"
        ; "focus"
        ; "in"
        ; "inductive"
        ; "infix"
        ; "injective"
        ; "left"
        ; "let"
        ; "off"
        ; "on"
        ; "open"
        ; "opaque"
        ; "prefix"
        ; "print"
        ; "private"
        ; "proofterm"
        ; "protected"
        ; "prover"
        ; "prover_timeout"
        ; "quantifier"
        ; "refine"
        ; "reflexivity"
        ; "require"
        ; "rewrite"
        ; "right"
        ; "rule"
        ; "sequential"
        ; "set"
        ; "simpl"
        ; "solve"
        ; "symbol"
        ; "symmetry"
        ; "type"
        ; "TYPE"
        ; "unif_rule"
        ; "verbose"
        ; "why3"
        ; "with" ]
    in
    fun s ->
    (* NOTE this function may be optimised using a map, a hashtable, or using
       [match%sedlex]. *)
      List.mem_sorted String.compare s kws

  (** [is_debug_flag s] is true if [s] is a debug flag of the form [+...] or
      [-...] where the dots are a sequence of letters. *)
  let is_debug_flag : string -> bool = fun s ->
    let lexbuf = Utf8.from_string s in
    match%sedlex lexbuf with
    | ('+' | '-'), Plus lowercase -> true
    | _ -> false

  (** [split_qid b] splits buffer [b] on dots, parsing identifiers between
      them. Each identifier is translated to a string, attached to a boolean
      which indicates whether it was escaped. *)
  let split_qid : string -> (string * bool) list = fun s ->
    String.split_on_char '.' s |> List.map unquote

  (** [tail buf] returns the utf8 string formed from [buf] dropping its first
      codepoint. *)
  let tail : lexbuf -> string = fun buf ->
    Utf8.sub_lexeme buf 1 (lexeme_length buf - 1)

  let token buf =
    nom buf;
    match%sedlex buf with

    (* end of file *)

    | eof -> EOF

    (* keywords *)

    | "abort" -> ABORT
    | "admit" -> ADMIT
    | "apply" -> APPLY
    | "as" -> AS
    | "assert" -> ASSERT
    | "assertnot" -> ASSERT_NOT
    | "assume" -> ASSUME
    | "begin" -> BEGIN
    | "builtin" -> BUILTIN
    | "compute" -> COMPUTE
    | "constant" -> CONSTANT
    | "debug" -> DEBUG
    | "end" -> END
    | "fail" -> FAIL
    | "flag" -> FLAG
    | "focus" -> FOCUS
    | "in" -> IN
    | "inductive" -> INDUCTIVE
    | "infix" -> INFIX
    | "injective" -> INJECTIVE
    | "left" -> ASSOC(Pratter.Left)
    | "let" -> LET
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
    | "set" -> SET
    | "simpl" -> SIMPL
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
    | '+', Plus alphabet -> DEBUG_FLAGS(true, tail buf)
    | '-', Plus alphabet -> DEBUG_FLAGS(false, tail buf)
    | integer -> INT(int_of_string (Utf8.lexeme buf))
    | float -> FLOAT(float_of_string (Utf8.lexeme buf))
    | stringlit ->
        (* Remove the quotes from [lexbuf] *)
        STRINGLIT(Utf8.sub_lexeme buf 1 (lexeme_length buf - 2))

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
    | '_' -> WILD

    (* identifiers *)

    | id -> ID(Utf8.lexeme buf, false)
    | '@', id -> QID_EXPL([tail buf, false])
    | '@', path -> QID_EXPL(split_qid (tail buf))
    | '?', id -> ID_META(tail buf)
    | '$', id -> ID_PAT(tail buf)
    | path -> QID(split_qid (Utf8.lexeme buf))
    | escid ->
        (* Remove the escape markers [{|] and [|}] from [lexbuf]. *)
        ID(Utf8.sub_lexeme buf 2 (lexeme_length buf - 4), true)

    (* invalid token *)

    | _ ->
        let loc = lexing_positions buf in
        let loc = locate loc in
        raise (SyntaxError(Pos.make (Some(loc)) (Utf8.lexeme buf)))

  (* Using the default case to lex identifiers result in a *very* slow lexing.
     This is why a regular expression which includes many characters is
     preferred over using anything for identifiers. *)

  let lexer = with_tokenizer token

  let unquote s = fst (unquote s)
end
include Lp_lexer
