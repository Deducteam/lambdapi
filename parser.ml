(** Parsing functions. *)

open Console
open Files

(** Parser-level representation of terms (and patterns). *)
type p_term =
  | P_Vari of string list * string
  | P_Type
  | P_Prod of string * p_term * p_term
  | P_Abst of string * p_term option * p_term
  | P_Appl of p_term * p_term
  | P_Wild

(* NOTE: the [P_Vari] constructor is used for variables (with an empty  module
   path), and for symbols. The [P_Wild] constructor corresponds to the wildard
   pattern ['_']. *)

(** [ident] is an atomic parser for an identifier (for example variable name).
    It accepts (and returns as semantic value) any non-empty strings formed of
    letters, decimal digits, and the ['_'] and ['''] characters. Note that the
    special identifiers ["Type"] and ["_"] are rejected (since reserved). *)
let parser ident = id:''[_'a-zA-Z0-9]+'' ->
  if List.mem id ["Type"; "_"] then Earley.give_up (); id

(** [qident] is an atomic parser for a qualified identifier, or in other words
    an identifier that may be preceeded by a module path.  The different parts
    are formed of the same characters as identifiers ([ident]), separated with
    the ['.'] character. *)
let parser qident = id:''\([_'a-zA-Z0-9]+[.]\)*[_'a-zA-Z0-9]+'' ->
  let fs = List.rev (String.split_on_char '.' id) in
  let (fs,x) = (List.rev (List.tl fs), List.hd fs) in
  if List.mem id ["Type"; "_"] then Earley.give_up (); (fs,x)

(** [_wild_] is an atomic parser for the special ["_"] identifier. *)
let parser _wild_ = s:''[_][_a-zA-Z0-9]*'' ->
  if s <> "_" then Earley.give_up ()

(** [_Type_] is an atomic parser for the special ["Type"] identifier. *)
let parser _Type_ = s:''[T][y][p][e][_a-zA-Z0-9]*'' ->
  if s <> "Type" then Earley.give_up ()

(** [_def_] is an atomic parser for the ["def"] keyword. *)
let parser _def_ = s:''[d][e][f][_a-zA-Z0-9]*'' ->
  if s <> "def" then Earley.give_up ()

(** [_thm_] is an atomic parser for the ["thm"] keyword. *)
let parser _thm_ = s:''[t][h][m][_a-zA-Z0-9]*'' ->
  if s <> "thm" then Earley.give_up ()

(** [expr p] is a parser for an expression at priority [p]. *)
let parser expr (p : [`Func | `Appl | `Atom]) =
  (* Variable *)
  | (fs,x):qident
      when p = `Atom -> P_Vari(fs,x)
  (* Type constant *)
  | _Type_
      when p = `Atom -> P_Type
  (* Product *)
  | x:{ident ":"}?["_"] a:(expr `Appl) "->" b:(expr `Func)
      when p = `Func -> P_Prod(x,a,b)
  (* Wildcard *)
  | _wild_
      when p = `Atom -> P_Wild
  (* Abstraction *)
  | x:ident a:{":" (expr `Func)}? "=>" t:(expr `Func)
      when p = `Func -> P_Abst(x,a,t)
  (* Application *)
  | t:(expr `Appl) u:(expr `Atom)
      when p = `Appl -> P_Appl(t,u)
  (* Parentheses *)
  | "(" t:(expr `Func) ")"
      when p = `Atom
  (* Coercions *)
  | t:(expr `Appl)
      when p = `Func
  | t:(expr `Atom)
      when p = `Appl

(** [expr] is the entry point of the parser for expressions, which include all
    terms, types and patterns. *)
let expr = expr `Func

(** Representation of a reduction rule, with its context. *)
type p_rule = (string * p_term option) list * p_term * p_term

(** Representation of a toplevel command. *)
type p_cmd =
  (** Static symbol declaration. *)
  | P_NewSym of string * p_term
  (** Definable symbol declaration. *)
  | P_NewDef of string * p_term
  (** Rewriting rules declaration. *)
  | P_Rules  of p_rule list
  (** Quick definition. *)
  | P_Defin  of string * p_term option * p_term
  (** Import an external signature. *)
  | P_Import of module_path
  (** Set debugging flags. *)
  | P_Debug  of bool * string
  (** Set the verbosity level. *)
  | P_Verb   of int
  (** Type-checking command. *)
  | P_Check  of p_term * p_term
  (** Type inference command. *)
  | P_Infer  of p_term
  (** Normalisation command. *)
  | P_Eval   of p_term
  (** Convertibility command. *)
  | P_Conv   of p_term * p_term
  (** Unimplemented command. *)
  | P_Other  of string

(** [ty_ident] is a parser for an (optionally) typed identifier. *)
let parser ty_ident = id:ident a:{":" expr}?

(** [context] is a parser for a rewriting rule context. *)
let parser context = {x:ty_ident xs:{"," ty_ident}* -> x::xs}?[[]]

(** [rule] is a parser for a single rewriting rule. *)
let parser rule = _:{"{" ident "}"}? "[" xs:context "]" t:expr "-->" u:expr

(** [def_def] is a parser for one specifc syntax of symbol definition. *)
let parser def_def =
  xs:{"(" ident ":" expr ")"}* ao:{":" ao:expr}? ":=" t:expr ->
    let t = List.fold_right (fun (x,a) t -> P_Abst(x, Some(a), t)) xs t in
    let ao =
      match ao with
      | None    -> None
      | Some(a) -> Some(List.fold_right (fun (x,a) b -> P_Prod(x,a,b)) xs a)
    in
    (ao, t)

(** [mod_path] is a parser for a module path. *)
let parser mod_path = path:''\([-_'a-zA-Z0-9]+[.]\)*[-_'a-zA-Z0-9]+'' ->
  String.split_on_char '.' path

(** [cmp] parses a single toplevel command. *)
let parser cmd =
  | x:ident ":" a:expr                   -> P_NewSym(x,a)
  | _def_ x:ident ":" a:expr             -> P_NewDef(x,a)
  | _def_ x:ident (ao,t):def_def         -> P_Defin(x,ao,t)
  | _thm_ x:ident (ao,t):def_def         -> P_Defin(x,ao,t)
  | rs:rule+                             -> P_Rules(rs)
  | "#REQUIRE" path:mod_path             -> P_Import(path)
  | "#DEBUG" f:''[+-]'' s:''[a-z]+''     -> P_Debug(f = "+", s)
  | "#VERBOSE" n:''[-+]?[0-9]+''         -> P_Verb(int_of_string n)
  | "#CHECK" t:expr "," a:expr           -> P_Check(t,a)
  | "#INFER" t:expr                      -> P_Infer(t)
  | "#EVAL" t:expr                       -> P_Eval(t)
  | "#CONV" t:expr "," u:expr            -> P_Conv(t,u)
  | c:"#NAME" _:ident                    -> P_Other(c)
  | c:"#STEP" _:expr                     -> P_Other(c)
  | c:"#SNF" _:expr                      -> P_Other(c)
  | c:"#WHNF" _:expr                     -> P_Other(c)
  | c:"#HNF" _:expr                      -> P_Other(c)
  | c:"#NSTEPS" "#"-''[0-9]+'' _:expr    -> P_Other(c)

(** Blank function for basic blank characters (' ', '\t', '\r' and '\n')
    and line comments starting with "//". *)
let blank buf pos =
  let rec fn state prev ((buf0, pos0) as curr) =
    let open Input in
    let (c, buf1, pos1) = read buf0 pos0 in
    let next = (buf1, pos1) in
    match (state, c) with
    (* Basic blancs. *)
    | (`Ini, ' '   )
    | (`Ini, '\t'  )
    | (`Ini, '\r'  )
    | (`Ini, '\n'  ) -> fn `Ini curr next
    (* Opening comment. *)
    | (`Ini, '('   ) -> fn `Opn curr next
    | (`Opn, ';'   ) -> fn `Com curr next
    (* Closing comment. *)
    | (`Com, ';'   ) -> fn `Cls curr next
    | (`Cls, ')'   ) -> fn `Ini curr next
    | (`Cls, _     ) -> fn `Com curr next
    (* Other. *)
    | (`Com, '\255') -> fatal "Unclosed comment...\n"
    | (`Com, _     ) -> fn `Com curr next
    | (`Opn, _     ) -> prev
    | (`Ini, _     ) -> curr
  in
  fn `Ini (buf, pos) (buf, pos)

(** [parse_file fname] attempts to parse the file [fname], to obtain a list of
    toplevel commands. In case of failure, a graceful error message containing
    the error position is displayerd and the program fails. *)
let parse_file : string -> p_cmd list =
  Earley.(handle_exception (parse_file (parser {l:cmd "."}*) blank))
