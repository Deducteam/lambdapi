(** Lexer for Lambdapi syntax. Uses Sedlex, a Utf8 friendly lexer. Some helper
    functions to check if a string conflicts with the syntax are also
    provided. *)
open Sedlexing
open Pos

type token =
  | EOF
  | L_PAREN | R_PAREN | L_SQ_BRACKET | R_SQ_BRACKET
  | L_CU_BRACKET | R_CU_BRACKET
  | APPLY | ARROW | AS | ASSERT | ASSERT_NOT | ASSIGN | ASSOC of Syntax.assoc
  | AT
  | BUILTIN | BACKQUOTE
  | COLON | COMMA | COMPUTE | COMPUTE_TYPE | CONSTANT
  | DEBUG_FLAGS of (bool * string)
  (** Flags such as [+eiu] or [-eiu]. *)
  | DEFINITION | DOLLAR | DOT
  | EQUIV
  | FAIL | FLAG | FLOAT of float | FOCUS
  | ID of (string * bool)
   (** Boolean is true if ident is escaped *)
  | IN | INFERTYPE | INFIX | INJECTIVE | INT of int | INTRO
  | LAMBDA | LET
  | OPEN
  | PI | PREFIX | PRINT | PRIVATE | PROOF | PROOF_END of Syntax.p_proof_end
  | PROOFTERM | PROTECTED | PROVER | PROVER_TIMEOUT
  | QUESTION_MARK
  | REFINE | REFL | REQUIRE | REWRITE | RULE
  | SEMICOLON | SEQUENTIAL | SET | SIMPL | STRINGLIT of string
  | SWITCH of bool
  (** [on] or [off], for flags. *)
  | SYMMETRY | SYMBOL
  | THEOREM | TYPE
  | UNIF_RULE
  | VERBOSE
  | WHY3 | WILD | WITH

exception SyntaxError of strloc

module Lp_lexer : sig
  val is_escaped : string -> bool
  val is_identifier : string -> bool
  val is_debug_flag : string -> bool
  val lexer : lexbuf -> unit -> token * Lexing.position * Lexing.position
end = struct
  let digit = [%sedlex.regexp? '0' .. '9']
  let integer = [%sedlex.regexp? Plus digit]
  let superscript = [%sedlex.regexp? 0x2070 | 0x00b9 | 0x00b2 | 0x00b3
                                   | 0x2074 .. 0x207c]
  let subscript = [%sedlex.regexp? 0x208 .. 0x208c]
  let alphabet = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
  (* NOTE: lambda character now counts as a letter, so a sequence λx is an
     identifier, so [λx t u,] fails on unexpected token [,]. But [λ x t u,]
     works. *)
  (* REVIEW: decide which set of unicode characters to use. *)
  let letter = [%sedlex.regexp? lowercase | uppercase | '-' | '\''
                              | math | subscript | superscript]
  let id = [%sedlex.regexp? (letter | '_'), Star (letter | digit | '_')]
  let escid =
    [%sedlex.regexp? "{|", Star (Compl '|' | '|', Compl '}'), Star '|', "|}"]
  let stringlit = [%sedlex.regexp? '"', Star (Compl ('"' | '\n')), '"']
  let float = [%sedlex.regexp? integer, Opt ('.', integer)]
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

  (** [is_identifier s] is true if [s] is an identifier. *)
  let is_identifier : string -> bool = fun s ->
    let lexbuf = Sedlexing.Utf8.from_string s in
    match%sedlex lexbuf with
    | id -> true
    | _ -> false

  (** [is_debug_flag s] is true if [s] is a debug flag of the form [+...] or
      [-...] where the dots are a sequence of letters. *)
  let is_debug_flag : string -> bool = fun s ->
    let lexbuf = Utf8.from_string s in
    match%sedlex lexbuf with
    | ('+' | '-'), Plus lowercase -> true
    | _ -> false

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
    | '@' -> AT
    | '?' -> QUESTION_MARK
    | '$' -> DOLLAR
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
    | "assume" -> INTRO
    | "simpl" -> SIMPL
    | "refine" -> REFINE
    | "apply" -> APPLY
    | "proof" -> PROOF
    | "reflexivity" -> REFL
    | "symmetry" -> SYMMETRY
    | "refine" -> REFINE
    | "why3" -> WHY3
    | "as" -> AS
    | "assert" -> ASSERT
    | "assertnot" -> ASSERT_NOT
    | "compute" -> COMPUTE
    | "type" -> COMPUTE_TYPE
    | "unif_rule" -> UNIF_RULE
    | "theorem" -> THEOREM
    | "in" -> IN
    | "on" -> SWITCH(true)
    | "off" -> SWITCH(false)
    | "qed" -> PROOF_END(Syntax.P_proof_qed)
    | "set" -> SET
    | "let" -> LET
    | "flag" -> FLAG
    | "type" -> COMPUTE_TYPE
    | "right" -> ASSOC(Syntax.Assoc_right)
    | "left" -> ASSOC(Syntax.Assoc_left)
    | "infix" -> INFIX
    | "TYPE" -> TYPE
    | "with" -> WITH
    | "rule" -> RULE
    | "open" -> OPEN
    | "prover" -> PROVER
    | "verbose" -> VERBOSE
    | "prefix" -> PREFIX
    | "builtin" -> BUILTIN
    | "symbol" -> SYMBOL
    | "require" -> REQUIRE
    | "definition" -> DEFINITION
    | "constant" -> CONSTANT
    | "injective" -> INJECTIVE
    | "protected" -> PROTECTED
    | "private" -> PRIVATE
    | "sequential" -> SEQUENTIAL
    | stringlit ->
        (* Remove the quotes from [lexbuf] *)
        STRINGLIT(Utf8.sub_lexeme buf 1 (lexeme_length buf - 2))
    | integer -> INT(int_of_string (Utf8.lexeme buf))
    | float -> FLOAT(float_of_string (Utf8.lexeme buf))
    | id -> ID(Utf8.lexeme buf, false)
    | escid -> ID(Utf8.lexeme buf, true)
    | _ ->
        (* REVIEW: verify position. *)
        let loc = lexing_positions buf in
        let loc = locate loc in
        raise (SyntaxError(Pos.make (Some(loc)) (Utf8.lexeme buf)))

  let lexer = with_tokenizer token
end
include Lp_lexer
