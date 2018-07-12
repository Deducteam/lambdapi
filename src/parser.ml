(** Parsing functions. *)

open Timed
open Console
open Files
open Pos

(** Logging function for the parser. *)
let log_pars = new_logger 'p' "pars" "debugging information for the parser"
let log_pars = log_pars.logger

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

(** Parser-level representation of terms (and patterns). *)
type p_term = p_term_aux loc
 and p_term_aux =
  | P_Vari of qident
  | P_Type
  | P_Prod of strloc * p_term option * p_term
  | P_Abst of strloc * p_term option * p_term
  | P_Appl of p_term * p_term
  | P_Wild
  | P_Meta of strloc * p_term array

(* NOTE: the [P_Vari] constructor is used for variables (with an empty  module
   path), and for symbols. The [P_Wild] constructor corresponds to a  wildcard
   pattern or to a fresh metavariable. *)

(** [get_args t] decomposes the {!type:p_term} [t] into a head term and a list
    of arguments. Note that in the returned pair [(h,args)],  [h] can never be
    a {!constr:P_Appl} node. *)
let get_args : p_term -> p_term * (Pos.popt * p_term) list = fun t ->
  let rec get_args acc t =
    match t.elt with
    | P_Appl(u,v) -> get_args ((t.pos,v)::acc) u
    | _           -> (t, acc)
  in get_args [] t

(** [add_args t args] builds the application of the {!type:p_term} [t] to  the
    arguments [args]. When [args] is empty, the returned value is (physically)
    equal to [t]. *)
let add_args : p_term -> (Pos.popt * p_term) list -> p_term = fun t args ->
  let rec add_args t args =
    match args with
    | []      -> t
    | (p,u)::args -> add_args (Pos.make p (P_Appl(t,u))) args
  in add_args t args

(** [build_prod xs a] build a product by abstracting away the arguments of the
    list [xs] on the body [a]. *)
let build_prod : (strloc * p_term option) list -> p_term -> p_term =
  List.fold_right (fun (x,a) b -> Pos.none (P_Prod(x,a,b)))

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
let _thm_       = keyword "thm"
let _CHECK_     = command "CHECK"
let _CHECKNOT_  = command "CHECKNOT"
let _ASSERT_    = command "ASSERT"
let _ASSERTNOT_ = command "ASSERTNOT"
let _REQUIRE_   = command "REQUIRE"
let _INFER_     = command "INFER"
let _EVAL_      = command "EVAL"
let _NAME_      = command "NAME"
let _PROOF_     = command "PROOF"
let _PRINT_     = command "PRINT"
let _REFINE_    = command "REFINE"
let _SIMPL_     = command "SIMPL"
let _QED_       = command "QED"
let _FOCUS_     = command "FOCUS"

(** [meta] is an atomic parser for a metavariable identifier. *)
let parser meta = "?" - id:''[a-zA-Z][_'a-zA-Z0-9]*'' -> in_pos _loc id

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
      when p >= PFunc -> in_pos _loc (P_Prod(x,Some(a),b))
  | "!" x:ident a:{":" (expr PFunc)}? "," b:(expr PFunc)
      when p >= PFunc -> in_pos _loc (P_Prod(x,a,b))
  (* Wildcard *)
  | _wild_
      when p >= PAtom -> in_pos _loc P_Wild
  (* Abstraction *)
  | x:ident a:{":" (expr PFunc)}? "=>" t:(expr PFunc)
      when p >= PFunc -> in_pos _loc (P_Abst(x,a,t))
  (* Application *)
  | t:(expr PAppl) u:(expr PAtom)
      when p >= PAppl -> in_pos _loc (P_Appl(t,u))
  (* Metavariable *)
  | m:meta e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Meta(m, Array.of_list e))
  (* Parentheses *)
  | "(" t:(expr PFunc) ")"
      when p >= PAtom

(** [env] is a parser for a metavariable environment. *)
and parser env = "[" t:(expr PAppl) ts:{"," (expr PAppl)}* "]" -> t::ts

(** [expr] is the entry point of the parser for expressions, which include all
    terms, types and patterns. *)
let expr = expr PFunc

(** Representation of a reduction rule, with its context. *)
type old_p_rule = (strloc * p_term option) list * p_term * p_term
type p_rule = p_term * p_term

let opaque = true
let const  = true

(** Representation of a toplevel command. *)
type p_cmd =
  (** Symbol declaration (constant when the boolean is [true]). *)
  | P_SymDecl  of bool * strloc * p_term
  (** Quick definition (opaque when the boolean is [true]). *)
  | P_SymDef   of bool * strloc * p_term option * p_term
  (** Rewriting rules declaration. *)
  | P_Rules    of p_rule list
  | P_OldRules of old_p_rule list
  (** Require an external signature. *)
  | P_Require   of module_path
  (** Type inference command. *)
  | P_Infer    of p_term * Eval.config
  (** Normalisation command. *)
  | P_Eval     of p_term * Eval.config
  (** Type-checking command. *)
  | P_TestType of bool * bool * p_term * p_term
  (** Convertibility command. *)
  | P_TestConv of bool * bool * p_term * p_term
  (** Unimplemented command. *)
  | P_Other    of strloc
  (** Start a proof. *)
  | P_StartProof of strloc * p_term
  (** Print focused goal. *)
  | P_PrintFocus
  (** Refine the focused goal. *)
  | P_Refine of p_term
  (** Normalize the focused goal. *)
  | P_Simpl
  (** Focus on a goal. *)
  | P_Focus of int
  (** End the proof. *)
  | P_EndProof

(** [ty_ident] is a parser for an (optionally) typed identifier. *)
let parser ty_ident = id:ident a:{":" expr}?

(** [rule] is a parser for a single rewriting rule. *)
let parser rule = t:expr "-->" u:expr

(** [context] is a parser for a rewriting rule context. *)
let parser context = {x:ty_ident xs:{"," ty_ident}* -> x::xs}?[[]]

(** [old_rule] is a parser for a single rewriting rule (old syntax). *)
let parser old_rule =
  _:{"{" ident "}"}? "[" xs:context "]" t:expr "-->" u:expr

let parser arg =
  | "(" x:ident ":" a:expr ")" -> (x, Some(a))
  | x:ident                    -> (x, None   )

(** [definition] is a parser for one specifc syntax of symbol definition. *)
let parser definition = xs:arg* ao:{":" expr}? ":=" t:expr ->
  let fn (x,a) t = Pos.none (P_Abst(x,a,t)) in
    let t = List.fold_right fn xs t in
    let ao =
      match ao with
      | None    -> None
      | Some(a) -> Some(build_prod xs a)
    in
    (ao, t)

(** [mod_path] is a parser for a module path. *)
let parser mod_path = path:''\([-_'a-zA-Z0-9]+[.]\)*[-_'a-zA-Z0-9]+'' ->
  String.split_on_char '.' path

(** [strategy] is a parser for an evaluation strategy name. *)
let parser strategy =
  | "WHNF" -> Eval.WHNF
  | "HNF"  -> Eval.HNF
  | "SNF"  -> Eval.SNF

(** [steps] is a parser for an integer, used in evaluation configuration. *)
let parser steps = n:''[0-9]+'' -> int_of_string n

(** [eval_config] is a parser for an evaluation configuration. *)
let parser eval_config =
  | EMPTY                             -> Eval.{strategy = SNF; steps = None}
  | "[" s:strategy n:{"," steps}? "]" -> Eval.{strategy = s  ; steps = n   }
  | "[" n:steps s:{"," strategy}? "]" ->
      let strategy = match s with None -> Eval.SNF | Some(s) -> s in
      Eval.{strategy; steps = Some(n)}

let parser check =
  | _CHECKNOT_  -> (false, true )
  | _CHECK_     -> (false, false)
  | _ASSERTNOT_ -> (true , true )
  | _ASSERT_    -> (true , false)

(** [cmd_aux] parses a single toplevel command. *)
let parser cmd_aux =
  | x:ident ":" a:expr               -> P_SymDecl(const,x,a)
  | _def_ x:ident ":" a:expr         -> P_SymDecl(not const,x,a)
  | _def_ x:ident (ao,t):definition  -> P_SymDef(not opaque,x,ao,t)
  | _thm_ x:ident (ao,t):definition  -> P_SymDef(opaque,x,ao,t)
  | r:rule rs:{"," rule}*            -> P_Rules(r::rs)
  | rs:old_rule+                     -> P_OldRules(rs)
  | _REQUIRE_ path:mod_path          -> P_Require(path)
  | (ia,mf):check t:expr "::" a:expr -> P_TestType(ia,mf,t,a)
  | (ia,mf):check t:expr "==" u:expr -> P_TestConv(ia,mf,t,u)
  | _INFER_ c:eval_config t:expr     -> P_Infer(t,c)
  | _EVAL_ c:eval_config t:expr      -> P_Eval(t,c)
  | _NAME_ _:ident                   -> P_Other(in_pos _loc "#NAME")
  | _PROOF_ x:ident ":" a:expr       -> P_StartProof(x,a)
  | _PRINT_                          -> P_PrintFocus
  | _REFINE_ t:expr                  -> P_Refine(t)
  | _SIMPL_                          -> P_Simpl
  | _FOCUS_ i:''[0-9]+''             -> P_Focus(int_of_string i)
  | _QED_                            -> P_EndProof

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

(** Accumulates parsing time for files (useful for profiling). *)
let total_time = Pervasives.ref 0.0

(** [parse_file fname] attempts to parse the file [fname], to obtain a list of
    toplevel commands. In case of failure, a graceful error message containing
    the error position is given through the [Fatal] exception. *)
let parse_file : string -> p_cmd loc list = fun fname ->
  Hashtbl.reset qid_map;
  try
    let (d, res) = Extra.time (Earley.parse_file cmd_list blank) fname in
    log_pars "parsed [%s] in %.2f seconds." fname d;
    Pervasives.(total_time := !total_time +. d); res
  with Earley.Parse_error(buf,pos) ->
    let loc = Some(Pos.locate buf pos buf pos) in
    fatal loc  "Parse error."

(** [parse_string fname str] attempts to parse the string [str] file to obtain
    a list of toplevel commands.  In case of failure, a graceful error message
    containing the error position is given through the [Fatal] exception.  The
    [fname] argument should contain a relevant file name for the error message
    to be constructed. *)
let parse_string : string -> string -> p_cmd loc list = fun fname str ->
  Hashtbl.reset qid_map;
  try Earley.parse_string ~filename:fname cmd_list blank str
  with Earley.Parse_error(buf,pos) ->
    let loc = Some(Pos.locate buf pos buf pos) in
    fatal loc "Parse error."
