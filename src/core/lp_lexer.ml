open Sedlexing
open Pos
open Extra

type token =
  | EOF
  | L_PAREN
  | R_PAREN
  | L_SQ_BRACKET
  | R_SQ_BRACKET
  | L_CU_BRACKET
  | R_CU_BRACKET
  | APPLY
  | ARROW
  | AS
  | ASSERT
  | ASSERTNOT
  | ASSIGN
  | ASSOC of Syntax.assoc
  | AT
  | BUILTIN
  | COLON
  | COMMA
  | COMPUTE
  | COMPUTE_TYPE
  | CONSTANT
  | DEFINITION
  | DOLLAR
  | DOT
  | FAIL
  | FLAG
  | FLOAT of float
  | FOCUS
  | ID of (string * bool)
   (** Boolean is true if ident is escaped *)
  | IN
  | INFERTYPE
  | INFIX
  | INJECTIVE
  | INT of int
  | INTRO
  | LAMBDA
  | LET
  | OPEN
  | PI
  | PREFIX
  | PRINT
  | PRIVATE
  | PROOF
  | PROOF_END of Syntax.p_proof_end
  | PROOFTERM
  | PROTECTED
  | PROVER
  | PROVER_TIMEOUT
  | QUESTION_MARK
  | REFINE
  | REFL
  | REQUIRE
  | REWRITE
  | RULE
  | SEMICOLON
  | SEQUENTIAL
  | SET
  | SIMPL
  | STRINGLIT of string
  | SWITCH of bool
  (** [on] or [off], for flags. *)
  | SYMMETRY
  | SYMBOL
  | THEOREM
  | TYPE
  | VERBOSE
  | WHY3
  | WILD
  | WITH

exception SyntaxError of strloc

let digit = [%sedlex.regexp? '0' .. '9']
let integer = [%sedlex.regexp? Plus digit]
let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let id = [%sedlex.regexp? letter, Star (letter | digit | '_')]
let escid =
  [%sedlex.regexp? "{|", Star (Compl '|' | '|', Compl '}'), Star '|', "|}"]
let stringlit = [%sedlex.regexp? '"', Star (Compl ('"' | '\n')), '"']
let float = [%sedlex.regexp? integer, Opt ('.', integer)]

(** [nom buf] eats whitespaces in buffer [buf]. *)
let rec nom : lexbuf -> unit = fun buf ->
  match%sedlex buf with
  | ' ' -> nom buf
  | '\t' -> nom buf
  | '\n' -> nom buf
  | '\r' -> nom buf
  | "\r\n" -> nom buf
  | _ -> ()

(** [is_escaped s] returns whether string [s] uses the escaped syntax. *)
let is_escaped: string -> bool = fun s ->
  String.length s >= 2 && String.sub s 0 2 = "{|"

let token buf =
  nom buf;
  match%sedlex buf with
  | eof -> EOF
  | "" -> EOF
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
  | 0x2254 (* ≔ *)-> ASSIGN
  | 0x21aa (* ↪ *) -> REWRITE
  | 0x2192 (* → *)-> ARROW
  | 0x03bb (* λ *)-> LAMBDA
  | 0x03a0 (* Π *)-> PI
  | "as" -> AS
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
      let len = lexeme_length buf in
      STRINGLIT(Utf8.sub_lexeme buf (len - 2) 1)
  | float -> FLOAT(float_of_string (Utf8.lexeme buf))
  | integer -> INT(int_of_string (Utf8.lexeme buf))
  | id -> ID(Utf8.lexeme buf, false)
  | escid -> ID(Utf8.lexeme buf, true)
  | _ ->
      let loc = lexing_positions buf in
      let loc = locate loc in
      raise (SyntaxError(Pos.make (Some(loc)) (Utf8.lexeme buf)))

let lexer = with_tokenizer token
