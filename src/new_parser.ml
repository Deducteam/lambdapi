open Pos

#define LOCATE locate

(** Keyword module. *)
module KW = Keywords.Make(
  struct
    let id_charset = Charset.from_string "a-zA-Z0-9_'"
    let reserved = []
  end)

(** Keyword declarations. *)
let _require_    = KW.create  "require"
let _open_       = KW.create  "open"
let _as_         = KW.special "as"
let _symbol_     = KW.create  "symbol"
let _definition_ = KW.create  "definition"
let _theorem_    = KW.create  "theorem"
let _rule_       = KW.create  "rule"
let _and_        = KW.create  "and"
let _assert_     = KW.create  "assert"
let _assertnot_  = KW.create  "assertnot"
let _const_      = KW.special "const"
let _inj_        = KW.special "injective"
let _TYPE_       = KW.create  "TYPE"
let _pos_        = KW.special "pos"
let _neg_        = KW.special "neg"
let _proof_      = KW.create  "proof"
let _qed_        = KW.create  "qed"
let _admit_      = KW.create  "admit"
let _abort_      = KW.create  "abort"
let _set_        = KW.create  "set"
let _wild_       = KW.create  "_"

(** Type of a (located) identifier. *)
type ident = strloc

(** Identifier. *)
let parser ident =
  | id:''[a-zA-Z_'][a-zA-Z0-9_']*'' -> KW.check id; in_pos _loc id

(** Type of a (qualified) identifier. *)
type qident = string list * ident

(** [path] parses a module path. *)
let parser path_elt = ''[a-zA-Z_'][a-zA-Z0-9_']*''
let parser path = m:path_elt ms:{"." path_elt}* -> m::ms

(** [qident] parses a single (possibly qualified) identifier. *)
let parser qident = ps:{path_elt "."}* x:ident

(** Symbol tag. *)
type symtag =
  | Sym_const
  | Sym_inj

(** [symtag] parses a single symbol tag. *)
let parser symtag =
  | _const_ -> Sym_const
  | _inj_   -> Sym_inj

(** Parser-level term representation. *)
type p_term = p_term_aux Pos.loc
and p_term_aux =
  | P_Type
  | P_Vari of qident
  | P_Wild
  | P_Meta of strloc * p_term array
  | P_Patt of strloc * p_term array
  | P_Appl of p_term * p_term
  | P_Impl of p_term * p_term
  | P_Abst of p_arg list * p_term
  | P_Prod of p_arg list * p_term

(** Synonym of [p_term] for semantic hints. *)
and p_type = p_term

(** Parser-level representation of a function argument. *)
and p_arg = ident * p_type option

let parser meta = "?" - id:''[a-zA-Z_'][a-zA-Z0-9_']*'' -> in_pos _loc id
let parser patt = "&" - id:''[a-zA-Z_'][a-zA-Z0-9_']*'' -> in_pos _loc id

(** Priority level for an expression (term or type). *)
type prio = PAtom | PAppl | PFunc

(** [term] is a parser for a term. *)
let parser term @(p : prio) =
  (* TYPE constant. *)
  | _TYPE_
      when p >= PAtom -> in_pos _loc P_Type
  (* Variable (or possibly qualified symbol). *)
  | x:qident
      when p >= PAtom -> in_pos _loc (P_Vari(x))
  (* Wildcard. *)
  | _wild_
      when p >= PAtom -> in_pos _loc P_Wild
  (* Metavariable. *)
  | m:meta e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Meta(m, Array.of_list e))
  (* Pattern (LHS) or pattern application (RHS). *)
  | p:patt e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Patt(p, Array.of_list e))
  (* Parentheses. *)
  | "(" t:(term PFunc) ")"
      when p >= PAtom -> t
  (* Application. *)
  | t:(term PAppl) u:(term PAtom)
      when p >= PAppl -> in_pos _loc (P_Appl(t,u))
  (* Implication. *)
  | a:(term PAppl) "⇒" b:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Impl(a,b))
  (* Products. *)
  | "∀" xs:arg* "," b:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Prod(xs,b))
  (* Abstraction. *)
  | "λ" xs:arg* "," t:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Abst(xs,t))

(** [env] is a parser for a metavariable environment. *)
and parser env = "[" t:(term PAppl) ts:{"," (term PAppl)}* "]" -> t::ts

(** [arg] parses a single function argument. *)
and parser arg =
  | x:ident                            -> (x, None   )
  | "(" x:ident ":" a:(term PFunc) ")" -> (x, Some(a))

let term = term PFunc

(** Parser-level rewriting rule representation. *)
type p_rule = p_term * p_term

(** [rule] is a parser for a single rewriting rule. *)
let parser rule =
  | l:term "→" r:term (* TODO *)

(** Parser-level representation of a proof tactic. *)
type p_tactic =
  | P_tac_intro of ident list
  (* TODO *)

(** [tactic] is a parser for a single tactic. *)
let parser tactic =
  | "intro" xs:ident* -> P_tac_intro(xs)

(** Parserl-level representation of a proof terminator. *)
type p_proof_end =
  | Proof_QED
  | Proof_admit
  | Proof_abort

(** [proof_end] is a parser for a proof terminator. *)
let parser proof_end = 
  | _qed_   -> Proof_QED
  | _admit_ -> Proof_admit
  | _abort_ -> Proof_abort

(** Parser-level representation of an assertion. *)
type p_assertion =
  | P_assert_typing of p_term * p_term
  | P_assert_conv   of p_term * p_term

(** [assertion] parses a single assertion. *)
let parser assertion =
  | t:term ":" a:term -> P_assert_typing(t,a)
  | t:term "≡" u:term -> P_assert_conv(t,u)

(** Parser-level representation of a configuration command. *)
type p_config =
  | P_verbose of int
  | P_debug   of bool * string

(** [config] pases a single configuration option. *)
let parser config =
  | "verbose" i:''[1-9][0-9]*'' -> P_verbose(int_of_string i)
  | "debug" d:''[-+][a-zA-Z]+'' ->
      let s = String.sub d 0 (String.length d - 1) in
      P_debug(d.[0] = '+', s)

(** Parser-level representation of a single command. *)
type p_cmd =
  | P_req    of bool * ident
  (** Require statement (opened if boolean is [true]). *)
  | P_req_as of ident * ident
  (** Require statement with alias (renaming). *)
  | P_open   of ident
  (** Open statement. *)
  | P_symbol of symtag list * ident * p_type
  (** Symbol declaration. *)
  | P_rules  of p_rule list
  (** Rewriting rule declarations. *)
  | P_def    of ident * p_arg list * p_type option * p_term
  (** Definition of a symbol (unfoldable). *)
  | P_thm    of ident * p_type * p_tactic list * p_proof_end
  (** Theorem with its proof. *)
  | P_assert of bool * p_assertion
  (** Assertion (must fail if boolean is [true]). *)
  | P_set    of p_config
  (** Set the configuration (debug, logging, ...). *)

let parser proof = _proof_ ts:{tactic ";"}* e:proof_end -> (ts,e)

let parser assert_must_fail =
  | _assert_    -> false
  | _assertnot_ -> true

(** [cmd] is a parser for a single command. *)
let parser cmd =
  | _require_ o:{_open_ -> true}?[false] m:ident           -> P_req(o,m)
  | _require_ m:ident _as_ n:ident                         -> P_req_as(m,n)
  | _open_ m:ident                                         -> P_open(m)
  | _symbol_ l:symtag* s:ident ":" a:term                  -> P_symbol(l,s,a)
  | _rule_ r:rule rs:{_:_and_ rule}*                       -> P_rules(r::rs)
  | _definition_ s:ident al:arg* ao:{":" term}? "=" t:term -> P_def(s,al,ao,t)
  | _theorem_ s:ident ":" a:term (ts,e):proof              -> P_thm(s,a,ts,e)
  | mf:assert_must_fail a:assertion                        -> P_assert(mf,a)
  | _set_ c:config                                         -> P_set(c)

(** [cmds] is a parser for multiple (located) commands. *)
let parser cmds = {c:cmd -> in_pos _loc c}*

(** [parse_file fname] parses the file [fname]. *)
let parse_file : string -> p_cmd loc list = fun fname ->
  let blank = Blanks.line_comments "//" in
  try Earley.parse_file cmds blank fname
  with Earley.Parse_error(buf,pos) ->
    let file = Input.filename buf in
    let line = Input.line_num buf in
    let col = Input.utf8_col_num buf pos in
    Printf.eprintf "%S %i:%i parse error...\n%!" file line col;
    exit 1

let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    let res = parse_file Sys.argv.(i) in
    Printf.printf "File %S has %i items.\n%!" Sys.argv.(i) (List.length res)
  done;
  Printf.printf "DONE.\n%!"
