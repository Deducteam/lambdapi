(** Parsing functions. *)

open Timed
open Extra
open Console
open Syntax
open Files
open Pos

#define LOCATE locate

(** Parser-level representation of a qualified identifier. *)
type qident = (module_path * string) loc

(** Hashtbl for the memoization of the parsing of qualified identifiers. It is
    a good idea to reset this table before parsing. *)
let qid_map : (string, module_path * string) Hashtbl.t = Hashtbl.create 31

(** [to_qident loc str] builds a qualified identifier from [str]. *)
let to_qid : string -> module_path * string = fun str ->
  try Hashtbl.find qid_map str with Not_found ->
  let fs = List.rev (String.split_on_char '.' str) in
  let qid = (List.rev (List.tl fs), List.hd fs) in
  Hashtbl.add qid_map str qid; qid

(** [ident] is an atomic parser for an identifier (for example variable name).
    It accepts (and returns as semantic value) any non-empty strings formed of
    letters, decimal digits, and the ['_'] and ['''] characters. Note that the
    special identifiers ["Type"] and ["_"] are rejected (since reserved). *)
let parser ident = id:''[_'a-zA-Z0-9]+'' ->
  if List.mem id ["Type"; "_"] then Earley.give_up (); in_pos _loc id

(** [qident] is an atomic parser for a qualified identifier, or in other words
    an identifier preceded by an optional module path. Its different parts are
    formed of the same characters as [ident], and are separated with the ['.']
    character. *)
let parser qident = id:''\([_'a-zA-Z0-9]+[.]\)*[_'a-zA-Z0-9]+'' ->
  let (_,id) as qid = to_qid id in
  if List.mem id ["Type"; "_"] then Earley.give_up ();
  in_pos _loc qid

(* NOTE we use an [Earley] regular expression to parse “qualified identifiers”
   for efficiency reasons. Indeed, there is an ambiguity in the parser (due to
   the final dot), and this is one way to resolve it by being “greedy”. *)

(** [keyword name] is an atomic parser for the keywork [name], not followed by
    any identifier character. *)
let keyword : string -> unit Earley.grammar = fun name ->
  let len = String.length name in
  if len < 1 then invalid_arg "Parser.keyword";
  let rec fn i buf pos =
    if i = len then
      match Input.get buf pos with
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> Earley.give_up ()
      | _                                           -> ((), buf, pos)
    else
      let (c, buf, pos) = Input.read buf pos in
      if c <> name.[i] then Earley.give_up ();
      fn (i+1) buf pos
  in
  let cs = Charset.singleton name.[0] in
  Earley.black_box (fn 0) cs false ("_" ^ name ^ "_")

(** [command name] is an atomic parser for the command ["#" ^ name]. *)
let command : string -> unit Earley.grammar = fun name -> keyword ("#" ^ name)

(* Defined keywords and commands. *)
let _wild_      = keyword "_"
let _Type_      = keyword "Type"
let _def_       = keyword "def"
let _inj_       = keyword "inj"
let _thm_       = keyword "thm"
let _in_        = command "in"
let _as_        = command "as"
let _CHECK_     = command "CHECK"
let _CHECKNOT_  = command "CHECKNOT"
let _ASSERT_    = command "ASSERT"
let _ASSERTNOT_ = command "ASSERTNOT"
let _REQUIRE_   = command "REQUIRE"
let _INFER_     = command "INFER"
let _EVAL_      = command "EVAL"

(** [meta] is an atomic parser for a metavariable identifier. *)
let parser meta = "?" - id:''[a-zA-Z][_'a-zA-Z0-9]*'' -> in_pos _loc id

(** [patt] is an atomic parser for a pattern variable identifier. *)
let parser patt = "&" - id:''[a-zA-Z][_'a-zA-Z0-9]*'' -> in_pos _loc id

(** Priority level for an expression. *)
type prio = PAtom | PAppl | PFunc

(** [expr p] is a parser for an expression at priority level [p]. The possible
    priority levels are [PFunc] (top level, including abstraction or product),
    [PAppl] (application) and [PAtom] (smallest priority). *)
let parser expr @(p : prio) =
  (* Variable *)
  | qid:qident
      when p >= PAtom -> in_pos _loc (P_Vari(qid))
  (* Type constant *)
  | _Type_
      when p >= PAtom -> in_pos _loc P_Type
  (* Product *)
  | x:{ident ":"}?[Pos.none "_"] a:(expr PAppl) "->" b:(expr PFunc)
      when p >= PFunc -> in_pos _loc (P_Prod([(x,Some(a))],b))
  (* Wildcard *)
  | _wild_
      when p >= PAtom -> in_pos _loc P_Wild
  (* Abstraction *)
  | x:ident a:{":" (expr PFunc)}? "=>" t:(expr PFunc)
      when p >= PFunc -> in_pos _loc (P_Abst([(x,a)],t))
  (* Application *)
  | t:(expr PAppl) u:(expr PAtom)
      when p >= PAppl -> in_pos _loc (P_Appl(t,u))
  (* Metavariable *)
  | m:meta e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Meta(m, Array.of_list e))
  (* Pattern variable. *)
  | x:patt e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Patt(x, Array.of_list e))
  (* Parentheses *)
  | "(" t:(expr PFunc) ")"
      when p >= PAtom

(** [env] is a parser for a metavariable environment. *)
and parser env = "[" t:(expr PAppl) ts:{"," (expr PAppl)}* "]" -> t::ts

(** [expr_appl] accepts application level expressions. *)
let expr_appl = expr PAppl

(** [expr] is the entry point of the parser for expressions, which include all
    terms, types and patterns. *)
let expr = expr PFunc

(** [ty_ident] is a parser for an (optionally) typed identifier. *)
let parser ty_ident = id:ident a:{":" expr}?

(** [context] is a parser for a rewriting rule context. *)
let parser context = {x:ty_ident xs:{"," ty_ident}* -> x::xs}?[[]]

(** [rule] is a parser for a single rewriting rule. *)
let parser rule = t:expr "-->" u:expr -> Pos.in_pos _loc (t,u)

(** [old_rule] is a parser for a single rewriting rule (old syntax). *)
let parser old_rule =
  _:{"{" ident "}"}? "[" xs:context "]" t:expr "-->" u:expr ->
    Pos.in_pos _loc (xs,t,u)

let parser arg =
  | "(" x:ident ":" a:expr ")" -> (x, Some(a))
  | x:ident                    -> (x, None   )

(** [mod_path] is a parser for a module path. *)
let parser mod_path = path:''\([-_'a-zA-Z0-9]+[.]\)*[-_'a-zA-Z0-9]+'' ->
  String.split_on_char '.' path

(** [strategy] is a parser for an evaluation strategy name. *)
let parser strategy =
  | "NONE" -> Eval.NONE
  | "WHNF" -> Eval.WHNF
  | "HNF"  -> Eval.HNF
  | "SNF"  -> Eval.SNF

(** [steps] is a parser for an integer, used in evaluation configuration. *)
let parser steps = n:''[0-9]+'' -> int_of_string n

(** [eval_config d] is a parser for an evaluation configuration with a default
    evaluation strategy set to be [d]. *)
let parser eval_config d =
  | EMPTY                             -> Eval.{strategy = d; steps = None}
  | "[" s:strategy n:{"," steps}? "]" -> Eval.{strategy = s; steps = n   }
  | "[" n:steps s:{"," strategy}? "]" ->
      Eval.{strategy = Option.get s d; steps = Some(n)}

(** [check] parses an assertion configuration (depending on command). *)
let parser assert_kw =
  | _ASSERTNOT_ -> true
  | _ASSERT_    -> false

(** [cmd_aux] parses a single toplevel command. *)
let parser cmd_aux =
  | _REQUIRE_ p:mod_path
      -> P_require(p, P_require_default)
  | x:ident ":" a:expr
      -> P_symbol([Sym_const], x, a)
  | _def_ x:ident ":" a:expr
      -> P_symbol([], x, a)
  | _inj_ x:ident ":" a:expr
      -> P_symbol([Sym_inj], x, a)
  | r:rule rs:{"," rule}*
      -> P_rules(r::rs)
  | rs:old_rule+
      -> P_rules(List.map translate_old_rule rs)
  | _def_ x:ident xs:arg* ao:{":" expr}? ":=" t:expr
      -> P_definition(false, x, xs, ao, t)
  | _thm_ x:ident xs:arg* ao:{":" expr}? ":=" t:expr
      -> P_definition(true , x, xs, ao, t)
  | mf:assert_kw t:expr_appl ":" a:expr
      -> P_assert(mf, P_assert_typing(t,a))
  | mf:assert_kw t:expr "==" u:expr
      -> P_assert(mf, P_assert_conv(t,u)  )
  | _INFER_ c:(eval_config Eval.NONE) t:expr
      -> P_infer(t, c)
  | _EVAL_  c:(eval_config Eval.SNF)  t:expr
      -> P_normalize(t, c)

(** [cmd] parses a single toplevel command with its position. *)
let parser cmd = c:cmd_aux -> in_pos _loc c

(** [cmd_list] parses a list of commands (the main entry point). *)
let parser cmd_list = {cmd "."}*

(** Blank function for ignoring basic blank characters ([' '], ['\t'], ['\r'],
    ['\n']) and (possibly nested) comments delimited by ["(;"] and [";)"]. *)
let blank buf pos =
  let rec fn state stack prev ((buf0, pos0) as curr) =
    let open Input in
    let (c, buf1, pos1) = read buf0 pos0 in
    let next = (buf1, pos1) in
    match (state, stack, c) with
    (* Basic blancs (not inside comment). *)
    | (`Ini, []  , ' '   )
    | (`Ini, []  , '\t'  )
    | (`Ini, []  , '\r'  )
    | (`Ini, []  , '\n'  ) -> fn `Ini stack curr next
    (* Opening of a comment (pushed on the stack). *)
    | (`Ini, _   , '('   ) -> fn `Opn stack curr next
    | (`Opn, _   , ';'   ) ->
        let loc = Pos.locate (fst prev) (snd prev) (fst curr) (snd curr) in
        fn `Ini (Some(loc)::stack) curr next
    (* Closing of a comment (popped from the stack). *)
    | (`Ini, _::_, ';'   ) -> fn `Cls stack curr next
    | (`Cls, _::s, ')'   ) -> fn `Ini s curr next
    (* Error on end of file if in a comment. *)
    | (_   , p::_, '\255') -> fatal p "Parse error (unclosed comment)."
    (* Ignoring any character inside comments. *)
    | (`Cls, []  , _     ) -> assert false (* impossible *)
    | (`Cls, _::_, _     )
    | (`Opn, _::_, _     ) -> fn `Ini stack curr next
    | (`Ini, _::_, _     ) -> fn `Ini stack curr next
    (* End of the blanks. *)
    | (`Opn, []  , _     ) -> prev
    | (`Ini, []  , _     ) -> curr
  in
  fn `Ini [] (buf, pos) (buf, pos)

(** [parse_file fname] attempts to parse the file [fname], to obtain a list of
    toplevel commands. In case of failure, a graceful error message containing
    the error position is given through the [Fatal] exception. *)
let parse_file : string -> Syntax.ast = fun fname ->
  Hashtbl.reset qid_map;
  try Earley.parse_file cmd_list blank fname
  with Earley.Parse_error(buf,pos) ->
    let loc = Some(Pos.locate buf pos buf pos) in
    fatal loc  "Parse error."

(** [parse_string fname str] attempts to parse the string [str] file to obtain
    a list of toplevel commands.  In case of failure, a graceful error message
    containing the error position is given through the [Fatal] exception.  The
    [fname] argument should contain a relevant file name for the error message
    to be constructed. *)
let parse_string : string -> string -> Syntax.ast = fun fname str ->
  Hashtbl.reset qid_map;
  try Earley.parse_string ~filename:fname cmd_list blank str
  with Earley.Parse_error(buf,pos) ->
    let loc = Some(Pos.locate buf pos buf pos) in
    fatal loc "Parse error."
