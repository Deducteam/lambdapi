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
  | UID of string
  | UID_META of Syntax.meta_ident
  | UID_PAT of string
  | QID of Path.t
  | ID_EXPL of Path.t

exception SyntaxError of strloc

(** Lexer for Lambdapi syntax. *)
module Lp_lexer : sig

  val is_uid : string -> bool
  (** [is_uid s] is [true] iff [s] is a regular identifier. *)

  val pp_uid : string Base.pp
  (** [pp_uid s] prints the uid [s], in escaped form if [s] is not a regular
   identifier. *)

  val is_identifier : string -> bool
  (** [is_identifier s] is [true] iff [s] is a valid identifier. *)

  val is_keyword : string -> bool
  (** [is_keyword s] returns [true] iff [s] is a keyword. *)

  val is_debug_flag : string -> bool
  (** [is_debug_flag s] is true iff [s] is a debug flag. *)

  val lexer : lexbuf -> unit -> token * Lexing.position * Lexing.position
  (** [lexer buf] is a lexing function on buffer [buf] that can be passed to
      a parser. *)

  val equiv : string
  (** [equiv] is the name of the symbol "≡" in unification rules. *)

  val cons : string
  (** [cons] is the name of the symbol ";" in unification rules. *)

  val unif_rule_path : Path.t
  (** [unif_rule_path] is the path for [equiv] and [cons].
     It cannot be entered by a user. *)

end = struct
  let digit = [%sedlex.regexp? '0' .. '9']
  let integer = [%sedlex.regexp? '0' | ('1' .. '9', Star digit)]
  let float = [%sedlex.regexp? integer, '.', Opt (integer)]
  let stringlit = [%sedlex.regexp? '"', Star (Compl ('"' | '\n')), '"']
  let comment = [%sedlex.regexp? "//", Star (Compl ('\n' | '\r'))]

  (* We define the set of UTF8 codepoints that make up identifiers. The
     builtin categories are described on the home page of sedlex
     @see https://github.com/ocaml-community/sedlex *)

  let alphabet = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
  let superscript =
    [%sedlex.regexp? 0x2070 | 0x00b9 | 0x00b2 | 0x00b3 | 0x2074 .. 0x207c]
  let subscript = [%sedlex.regexp? 0x208 .. 0x208c]
  let supplemental_punctuation = [%sedlex.regexp? 0x2e00 .. 0x2e52]
  let ascii_sub =
    [%sedlex.regexp? '-' | '\'' | '&' | '^' | '\\' | '*' | '%' | '#' | '~']
  let letter =
    [%sedlex.regexp? lowercase | uppercase | ascii_sub
                   | math | other_math | subscript | superscript
                   | supplemental_punctuation ]
  let regid = [%sedlex.regexp? (letter | '_'), Star (letter | digit | '_')]

  (* Once unescaped, escaped identifiers must not be empty, as the empty
     string is used in the path of ghost signatures. *)
  let escid =
    [%sedlex.regexp? "{|", Plus (Compl '|' | '|', Compl '}'), Star '|', "|}"]
  let non_user_id = ""
  let ghost_path s = [non_user_id; s]
  let unif_rule_path = ghost_path "unif_rule"
  let equiv = "≡"
  let cons = ";"

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

  let is_debug_flag : string -> bool = fun s ->
    let lexbuf = Utf8.from_string s in
    match%sedlex lexbuf with
    | ('+' | '-'), Plus lowercase -> true
    | _ -> false

  let is_uid : string -> bool = fun s ->
    s = non_user_id ||
    let lexbuf = Sedlexing.Utf8.from_string s in
    match%sedlex lexbuf with
    | uid -> true
    | _ -> false

  let pp_uid : string Base.pp = fun ppf s ->
    if is_uid s
    then Format.fprintf ppf "%s" s
    else Format.fprintf ppf "{|%s|}" s

  let is_identifier : string -> bool = fun s ->
    s = non_user_id ||
    let lexbuf = Sedlexing.Utf8.from_string s in
    match%sedlex lexbuf with
    | id -> true
    | _ -> false

  (** [tail buf] returns the utf8 string formed from [buf] dropping its
     first codepoints. *)
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

    | '+', Plus lowercase -> DEBUG_FLAGS(true, tail buf)
    | '-', Plus lowercase -> DEBUG_FLAGS(false, tail buf)
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

    (* Using the default case to lex identifiers result in a *very* slow
       lexing. This is why a regular expression which includes many characters
       is preferred over using anything for identifiers. *)

    | '?', uid -> UID_META(Syntax.Name(Escape.unescape(tail buf)))
    | '?', integer ->
        UID_META(Syntax.Numb(int_of_string(Escape.unescape(tail buf))))
    | '$', uid -> UID_PAT(Escape.unescape(tail buf))

    | '@', uid -> ID_EXPL([Escape.unescape(tail buf)])
    | '@', qid -> ID_EXPL(List.map Escape.unescape (Path.of_string(tail buf)))

    | uid -> UID(Escape.unescape(Utf8.lexeme buf))
    | qid -> QID(List.map Escape.unescape (Path.of_string(Utf8.lexeme buf)))

    (* invalid token *)

    | _ ->
        let loc = locate (lexing_positions buf) in
        raise (SyntaxError(Pos.make (Some(loc)) (Utf8.lexeme buf)))

  let lexer = with_tokenizer token

end
include Lp_lexer
