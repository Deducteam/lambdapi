(** Lexer for Lambdapi syntax. Uses Sedlex, a Utf8 friendly lexer. Some helper
    functions to check if a string conflicts with the syntax are also
    provided. *)
open Lplib
open Sedlexing
open Pos

type token =
  | EOF
  | L_PAREN | R_PAREN | L_SQ_BRACKET | R_SQ_BRACKET
  | L_CU_BRACKET | R_CU_BRACKET
  | ABORT | ADMIT | APPLY | ARROW | AS | ASSERT | ASSERT_NOT | ASSIGN
  | ASSOC of Pratter.associativity
  | BACKQUOTE | BUILTIN | BEGIN
  | COLON | COMMA | COMPUTE | COMPUTE_TYPE | CONSTANT
  | DEBUG | DEBUG_FLAGS of (bool * string)
  (** Flags such as [+eiu] or [-eiu]. Tuple constructor (with parens) is
      needed by Menhir. *)
  | DOT
  | END | EQUIV
  | FAIL | FLAG | FLOAT of float | FOCUS
  | ID of (string * bool)  (* Boolean is true if the identifier is escaped. *)
  | ID_EXPL of string | ID_META of string | ID_PAT of string
  | IN | INFERTYPE | INDUCTIVE | INFIX | INJECTIVE | INT of int | INTRO
  | LAMBDA | LET
  | OPAQUE | OPEN
  | PATH of (string * bool) list | PI | PREFIX | PRINT | PRIVATE
  | PROOFTERM | PROTECTED | PROVER | PROVER_TIMEOUT
  | QID_EXPL of (string * bool) list | QUANTIFIER
  | REFINE | REFL | REQUIRE | REWRITE | RULE
  | SEMICOLON | SEQUENTIAL | SET | SIMPL | STRINGLIT of string
  | SWITCH of bool
  (** [on] or [off], for flags. *)
  | SYMMETRY | SYMBOL
  | TYPE | TURNSTILE
  | UNIF_RULE
  | VBAR
  | VERBOSE
  | WHY3 | WILD | WITH

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
        [ "TYPE"
        ; "apply"
        ; "as"
        ; "assert"
        ; "assertnot"
        ; "assume"
        ; "builtin"
        ; "compute"
        ; "constant"
        ; "definition"
        ; "flag"
        ; "in"
        ; "inductive"
        ; "infix"
        ; "injective"
        ; "left"
        ; "let"
        ; "off"
        ; "on"
        ; "open"
        ; "prefix"
        ; "private"
        ; "proof"
        ; "protected"
        ; "prover"
        ; "prover_timeout"
        ; "qed"
        ; "refine"
        ; "refine"
        ; "reflexivity"
        ; "require"
        ; "rewrite"
        ; "right"
        ; "rule"
        ; "set"
        ; "sequential"
        ; "simpl"
        ; "symbol"
        ; "symmetry"
        ; "theorem"
        ; "type"
        ; "type"
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

  let token buf =
    nom buf;
    match%sedlex buf with
    | eof -> EOF
    | '(' -> L_PAREN
    | ')' -> R_PAREN
    | '[' -> L_SQ_BRACKET
    | ']' -> R_SQ_BRACKET
    | '{' -> L_CU_BRACKET
    | '}' -> R_CU_BRACKET
    | '_' -> WILD
    | ':' -> COLON
    | ',' -> COMMA
    | '.' -> DOT
    | ';' -> SEMICOLON
    | '|' -> VBAR
    | '`' -> BACKQUOTE
    | '+', Plus alphabet ->
        DEBUG_FLAGS(true, Utf8.sub_lexeme buf 1 (lexeme_length buf - 1))
    | '-', Plus alphabet ->
        DEBUG_FLAGS(false, Utf8.sub_lexeme buf 1 (lexeme_length buf - 1))
    | 0x2254 (* ≔ *) -> ASSIGN
    | 0x21aa (* ↪ *) -> REWRITE
    | 0x2192 (* → *) -> ARROW
    | 0x03bb (* λ *) -> LAMBDA
    | 0x03a0 (* Π *) -> PI
    | 0x2261 (* ≡ *) -> EQUIV
    | 0x22a2 (* ⊢ *) -> TURNSTILE
    | "abort" -> ABORT
    | "admit" -> ADMIT
    | "apply" -> APPLY
    | "as" -> AS
    | "assert" -> ASSERT
    | "assertnot" -> ASSERT_NOT
    | "assume" -> INTRO
    | "begin" -> BEGIN
    | "builtin" -> BUILTIN
    | "compute" -> COMPUTE
    | "constant" -> CONSTANT
    | "debug" -> DEBUG
    | "end" -> END
    | "flag" -> FLAG
    | "inductive" -> INDUCTIVE
    | "infix" -> INFIX
    | "in" -> IN
    | "injective" -> INJECTIVE
    | "left" -> ASSOC(Pratter.Left)
    | "let" -> LET
    | "off" -> SWITCH(false)
    | "on" -> SWITCH(true)
    | "opaque" -> OPAQUE
    | "open" -> OPEN
    | "prefix" -> PREFIX
    | "private" -> PRIVATE
    | "protected" -> PROTECTED
    | "prover" -> PROVER
    | "prover_timeout" -> PROVER_TIMEOUT
    | "quantifier" -> QUANTIFIER
    | "refine" -> REFINE
    | "refine" -> REFINE
    | "reflexivity" -> REFL
    | "require" -> REQUIRE
    | "rewrite" -> REWRITE
    | "right" -> ASSOC(Pratter.Right)
    | "rule" -> RULE
    | "sequential" -> SEQUENTIAL
    | "set" -> SET
    | "simpl" -> SIMPL
    | "symbol" -> SYMBOL
    | "symmetry" -> SYMMETRY
    | "type" -> COMPUTE_TYPE
    | "type" -> COMPUTE_TYPE
    | "TYPE" -> TYPE
    | "unif_rule" -> UNIF_RULE
    | "verbose" -> VERBOSE
    | "why3" -> WHY3
    | "with" -> WITH
    | id -> ID(Utf8.lexeme buf, false)
    | '@', id -> ID_EXPL(Utf8.sub_lexeme buf 1 (lexeme_length buf - 1))
    | '@', path ->
        QID_EXPL(split_qid (Utf8.sub_lexeme buf 1 (lexeme_length buf - 1)))
    | '?', id -> ID_META(Utf8.sub_lexeme buf 1 (lexeme_length buf - 1))
    | '$', id -> ID_PAT(Utf8.sub_lexeme buf 1 (lexeme_length buf - 1))
    | path -> PATH(split_qid (Utf8.lexeme buf))
    | integer -> INT(int_of_string (Utf8.lexeme buf))
    | float -> FLOAT(float_of_string (Utf8.lexeme buf))
    | stringlit ->
        (* Remove the quotes from [lexbuf] *)
        STRINGLIT(Utf8.sub_lexeme buf 1 (lexeme_length buf - 2))
    | escid ->
        (* Remove the escape markers [{|] and [|}] from [lexbuf]. *)
        ID(Utf8.sub_lexeme buf 2 (lexeme_length buf - 4), true)
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
