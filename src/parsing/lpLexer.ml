(** Lexer for Lambdapi syntax. Uses Sedlex, a Utf8 friendly lexer. Some helper
    functions to check if a string conflicts with the syntax are also
    provided. *)
open Lplib
open Sedlexing
open Common
open Pos

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
  | UID of string
  | UID_META of Syntax.meta_ident
  | UID_PAT of string
  | QID of Path.t
  | ID_EXPL of Path.t

exception SyntaxError of strloc

  let digit = [%sedlex.regexp? '0' .. '9']
  let nonzero_nat = [%sedlex.regexp? '1' .. '9', Star digit]
  let nat = [%sedlex.regexp? '0' | nonzero_nat]
  let float = [%sedlex.regexp? nat, '.', Opt (nat)]
  let stringlit = [%sedlex.regexp? '"', Star (Compl ('"' | '\n')), '"']
  let comment = [%sedlex.regexp? "//", Star (Compl ('\n' | '\r'))]

  (* Identifiers are defined by what cannot appear in them. *)
  let forbidden_letter = [%sedlex.regexp? Chars " ,;\r\t\n(){}[]:.`\""]
  let regid = [%sedlex.regexp? Plus (Compl forbidden_letter)]

  let is_regid : string -> bool = fun s ->
    let lexbuf = Sedlexing.Utf8.from_string s in
    match%sedlex lexbuf with
    | regid, eof -> true
    | _ -> false

  let uid_of_string : string -> string = fun s ->
    let s' = Escape.unescape s in if is_regid s' then s' else s

  let path_of_string : string -> Path.t = fun s ->
    List.map uid_of_string (Path.of_string s)

  (* Identifiers not compatible with Bindlib. *)
  let invalid_bindlib_id = [%sedlex.regexp? Star any, Plus '0', nat]

  let is_invalid_bindlib_id : string -> bool = fun s ->
    let lexbuf = Sedlexing.Utf8.from_string s in
    match%sedlex lexbuf with
    | invalid_bindlib_id, eof -> true
    | _ -> false

  (* unit tests *)
  let _ =
    assert (let f = is_invalid_bindlib_id in f "00" && f "01" && f "a01")

  (* Escaped identifiers must not be empty, as the empty string is used in the
     path of ghost signatures. *)
  let escid =
    [%sedlex.regexp? "{|", Plus (Compl '|' | '|', Compl '}'), Star '|', "|}"]
  let uid = [%sedlex.regexp? regid | escid]
  let qid = [%sedlex.regexp? uid, Plus ('.', uid)]
  let id = [%sedlex.regexp? uid | qid]

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

  let is_keyword : string -> bool =
    let kws =
      List.sort String.compare
        [ "abort"
        ; "admit"
        ; "admitted"
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
        ; "generalize"
        ; "have"
        ; "in"
        ; "induction"
        ; "inductive"
        ; "infix"
        ; "injective"
        ; "left"
        ; "let"
        ; "off"
        ; "on"
        ; "opaque"
        ; "open"
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
        ; "simplify"
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

  (** [tail buf] returns the utf8 string obtained by dropping the first
     codepoint in [buf]. *)
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
    | "admitted" -> ADMITTED
    | "apply" -> APPLY
    | "as" -> AS
    | "assert" -> ASSERT
    | "assertnot" -> ASSERTNOT
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

    | '+', Plus lowercase -> DEBUG_FLAGS(true, tail buf)
    | '-', Plus lowercase -> DEBUG_FLAGS(false, tail buf)
    | nat -> INT(int_of_string (Utf8.lexeme buf))
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

    | '?', nat -> UID_META(Syntax.Numb(int_of_string(tail buf)))
    | '?', uid -> UID_META(Syntax.Name(uid_of_string(tail buf)))
    | '$', uid -> UID_PAT(uid_of_string(tail buf))

    | '@', uid -> ID_EXPL[uid_of_string(tail buf)]
    | '@', qid -> ID_EXPL(path_of_string(tail buf))

    | uid -> UID(uid_of_string(Utf8.lexeme buf))
    | qid -> QID(path_of_string(Utf8.lexeme buf))

    (* invalid token *)

    | _ ->
        let loc = locate (lexing_positions buf) in
        raise (SyntaxError(Pos.make (Some(loc)) (Utf8.lexeme buf)))

  let lexer = with_tokenizer token
