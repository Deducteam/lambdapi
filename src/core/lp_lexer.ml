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
  | ABORT
  | ADMIT
  | APPLY
  | ARROW
  | AS
  | ASSERT
  | ASSERTNOT
  | ASSIGN
  | AT
  | COLON
  | COMMA
  | COMPUTE
  | CONSTANT
  | DEFINITION
  | DOLLAR
  | DOT
  | FAIL
  | FOCUS
  | ID of (string * bool)
   (** Boolean is true if ident is escaped *)
  | IN
  | INFERTYPE
  | INJECTIVE
  | INTRO
  | LAMBDA
  | LET
  | OPEN
  | PI
  | PRINT
  | PRIVATE
  | PROOF
  | PROOFTERM
  | PROTECTED
  | QED
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
  | SYMMETRY
  | SYMBOL
  | THEOREM
  | TYPE
  | WHY3
  | WILD
  | WITH

exception SyntaxError of strloc

let digit = [%sedlex.regexp? '0' .. '9']
let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let id = [%sedlex.regexp? letter, Star (letter | digit | '_')]
let escid =
  [%sedlex.regexp? "{|", Star (Compl '|' | '|', Compl '}'), Star '|', "|}"]
let qid = [%sedlex.regexp? Star (id | escid, '.'), id | escid]
let meta_id = [%sedlex.regexp? '?', id | escid]
let patt_id = [%sedlex.regexp? '$', id | escid]

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
  | "let" -> LET
  | "in" -> IN
  | "TYPE" -> TYPE
  | "rule" -> RULE
  | "open" -> OPEN
  | "symbol" -> SYMBOL
  | "require" -> REQUIRE
  | "definition" -> DEFINITION
  | "constant" -> CONSTANT
  | "injective" -> INJECTIVE
  | "protected" -> PROTECTED
  | "private" -> PRIVATE
  | "sequential" -> SEQUENTIAL
  | id -> ID(Utf8.lexeme buf, false)
  | escid -> ID(Utf8.lexeme buf, true)
  | _ ->
      let loc = lexing_positions buf in
      let loc = locate loc in
      raise (SyntaxError(Pos.make (Some(loc)) (Utf8.lexeme buf)))

let lexer = with_tokenizer token
