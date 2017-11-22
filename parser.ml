open Console

(* Parser-level representation of terms (and patterns). *)
type p_term =
  | P_Vari of string list * string
  | P_Type
  | P_Prod of string * p_term * p_term
  | P_Abst of string * p_term option * p_term
  | P_Appl of p_term * p_term
  | P_Wild

(* NOTE: the [P_Vari] constructor is used for variables (with an empty  module
   path) and for symbols.  The [P_Wild] corresponds to a wildard,  when a term
   is considered as a pattern. *)

(* [ident] is an atomic parser for an identifier (for example, variable name).
   It accepts (and returns as its semantic value) any non-empty strings formed
   of letters,  decimal digits, and the ['_'] and ['''] characters.  Note that
   ["Type"] and ["_"] are reserved identifiers, and they are thus rejected. *)
let parser ident = id:''[_'a-zA-Z0-9]+'' ->
  if List.mem id ["Type"; "_"] then Earley.give_up (); id

(* [qident] is an atomic parser for a qualified identifier (e.g. an identifier
   that may be preceeded by a module path. The different parts of the path and
   the identifier are build as for [ident] and separated by a ['.']. *)
let parser qident = id:''\([_'a-zA-Z0-9]+[.]\)*[_'a-zA-Z0-9]+'' ->
  let fs = List.rev (String.split_on_char '.' id) in
  let (fs,x) = (List.rev (List.tl fs), List.hd fs) in
  if List.mem id ["Type"; "_"] then Earley.give_up (); (fs,x)

(* [_wild_] is an atomic parser for the special ["_"] identifier. Note that it
   is only accepted if it is not followed by an identifier character. *)
let parser _wild_ = s:''[_][_a-zA-Z0-9]*'' ->
  if s <> "_" then Earley.give_up ()

(* [_Type_] is an atomic parser for the special ["Type"] identifier. Note that
   it is only accepted when it is not followed an identifier character. *)
let parser _Type_ = s:''[T][y][p][e][_a-zA-Z0-9]*'' ->
  if s <> "Type" then Earley.give_up ()

(* [expr p] is a parser for an expression at priority [p]. *)
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

(* [expr] is the entry point of the parser for expressions, including terms as
   well as types and patterns. *)
let expr = expr `Func

(* Representation of a toplevel item (symbol definition, command, ...). *)
type p_item =
  (* New symbol (static or definable). *)
  | NewSym  of bool * string * p_term
  (* New rewriting rules. *)
  | Rules   of p_rule list
  (* New definable symbol with its definition. *)
  | Defin   of string * p_term option * p_term
  (* Commands. *)
  | Check   of p_term * p_term
  | Infer   of p_term
  | Eval    of p_term
  | Conv    of p_term * p_term
  | Name    of string
  | Step    of p_term
  | Debug   of string
  | Require of string list

(* Representation of a reduction rule, with its context. *)
and p_rule = (string * p_term option) list * p_term * p_term

(* [ty_ident] is a parser for an (optionally) typed identifier. *)
let parser ty_ident = id:ident a:{":" expr}?

(* [context] is a parser for a rewriting rule context. *)
let parser context = {x:ty_ident xs:{"," ty_ident}* -> x::xs}?[[]]

(* [rule] is a parser for a single rewriting rule. *)
let parser rule = "[" xs:context "]" t:expr "-->" u:expr

(* [def_def] is a parser for one specifc syntax of symbol definition. *)
let parser def_def = xs:{"(" ident ":" expr ")"}* ":=" t:expr ->
  List.fold_right (fun (x,a) t -> P_Abst(x, Some(a), t)) xs t

let parser mod_path = path:''\([_'a-zA-Z0-9]+[.]\)*[_'a-zA-Z0-9]+'' ->
  String.split_on_char '.' path

(* [toplevel] parses a single toplevel item. *)
let parser toplevel =
  | x:ident ":" a:expr                      -> NewSym(false,x,a)
  | "def" x:ident ":" a:expr                -> NewSym(true ,x,a)
  | "def" x:ident ":" a:expr ":=" t:expr    -> Defin(x,Some(a),t)
  | "def" x:ident t:def_def                 -> Defin(x,None   ,t)
  | rs:rule+                                -> Rules(rs)
  | "#CHECK" t:expr "," a:expr              -> Check(t,a)
  | "#INFER" t:expr                         -> Infer(t)
  | "#EVAL" t:expr                          -> Eval(t)
  | "#CONV" t:expr "," u:expr               -> Conv(t,u)
  | "#NAME" id:ident                        -> Name(id)
  | "#STEP" t:expr                          -> Step(t)
  | "#SNF"  t:expr                          -> Eval(t)
  | "#DEBUG" s:''[a-z]+''                   -> Debug(s)
  | "#REQUIRE" path:mod_path                -> Require(path)

(* [full] is the main entry point of the parser. It accepts a list of toplevel
   items, each teminated by a ['.']. *)
let parser full = {l:toplevel "."}*

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

(* [parse_file fname] attempts to parse the file [fname],  to obtain a list of
   toplevel items. In case of failure, a standard parse error message is shown
   and then [exit 1] is called. *)
let parse_file : string -> p_item list =
  Earley.(handle_exception (parse_file full blank))
