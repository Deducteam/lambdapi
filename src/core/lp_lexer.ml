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
  | QID of (Syntax.p_module_path * string)
  | IN
  | INFERTYPE
  | INJECTIVE
  | INTRO
  | LAMBDA
  | LET
  | META of string
  | OPEN
  | PATT of string
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
let qid = [%sedlex.regexp? Star (id, '.'), id]
let escid =
  [%sedlex.regexp? "{|", Star (Compl '|' | '|', Compl '}'), Star '|', "|}"]
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
let is_escaped: string -> bool = fun _ -> assert false

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
  | 0x2254 (* ≔ *)-> ASSIGN
  | 0x21aa (* ↪ *) -> REWRITE
  | 0x2192 (* → *)-> ARROW
  | 0x03bb (* λ *)-> LAMBDA
  | 0x03a0 (* Π *)-> PI
  | "let" -> LET
  | "in" -> IN
  | "TYPE" -> TYPE
  | "rule" -> RULE
  | "symbol" -> SYMBOL
  | "definition" -> DEFINITION
  | "constant" -> CONSTANT
  | "injective" -> INJECTIVE
  | "protected" -> PROTECTED
  | "private" -> PRIVATE
  | "sequential" -> SEQUENTIAL
  (* We discard the sigils '?' and '$'. *)
  | meta_id -> META(String.tail (Utf8.lexeme buf))
  | patt_id -> PATT(String.tail (Utf8.lexeme buf))
  | id -> ID(Utf8.lexeme buf, false)
  | escid -> ID(Utf8.lexeme buf, true)
  | qid ->
      let mp = Utf8.lexeme buf in
      let elts = String.split_on_char '.' mp in
      let (sym, path) =
        match List.rev elts with
        | [] -> assert false
        | hd :: tl -> (hd, List.rev tl)
      in
      QID(List.map (fun e -> (e, is_escaped e)) path, sym)
  | _ ->
      let loc = lexing_positions buf in
      let loc = locate loc in
      raise (SyntaxError(Pos.make (Some(loc)) (Utf8.lexeme buf)))

let lexer = with_tokenizer token
