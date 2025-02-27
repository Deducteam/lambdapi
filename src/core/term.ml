(** Internal representation of terms.

   This module contains the definition of the internal representation of
   terms, together with smart constructors and low level operation. *)

open Lplib open Base open Extra
open Common open Debug

let log = Logger.make 'm' "term" "term building"
let log = log.pp

(** {3 Term (and symbol) representation} *)

(** Representation of a possibly qualified identifier. *)
type qident = Path.t * string

(** Pattern-matching strategy modifiers. *)
type match_strat =
  | Sequen
  (** Rules are processed sequentially: a rule can be applied only if the
      previous ones (in the order of declaration) cannot be. *)
  | Eager
  (** Any rule that filters a term can be applied (even if a rule defined
      earlier filters the term as well). This is the default. *)

(** Specify the visibility and usability of symbols outside their module. *)
type expo =
  | Public (** Visible and usable everywhere. *)
  | Protec (** Visible everywhere but usable in LHS arguments only. *)
  | Privat (** Not visible and thus not usable. *)

type side = Left | Right

(** Symbol properties. *)
type prop =
  | Defin (** Definable. *)
  | Const (** Constant. *)
  | Injec (** Injective. *)
  | Commu (** Commutative. *)
  | AC of side (** Associative and commutative. *)

(** Data of a binder. *)
type binder_info = {binder_name : string; binder_bound : bool}
type mbinder_info = {mbinder_name : string array; mbinder_bound : bool array}

let pr_bound = D.array (fun ppf b -> if b then out ppf "*" else out ppf "_")

(** Type for free variables. *)
type var = int * string

(** [compare_vars x y] safely compares [x] and [y]. Note that it is unsafe to
    compare variables using [Pervasive.compare]. *)
let compare_vars : var -> var -> int = fun (i,_) (j,_) -> Stdlib.compare i j

(** [eq_vars x y] safely computes the equality of [x] and [y]. Note that it is
    unsafe to compare variables with the polymorphic equality function. *)
let eq_vars : var -> var -> bool = fun x y -> compare_vars x y = 0

(** [new_var name] creates a new unique variable of name [name]. *)
let new_var : string -> var =
  let n = Stdlib.ref 0 in fun name -> incr n; !n, name

(** [new_var_ind s i] creates a new [var] of name [s ^ string_of_int i]. *)
let new_var_ind : string -> int -> var = fun s i ->
  new_var (Escape.add_prefix s (string_of_int i))

(** [base_name x] returns the base name of variable [x]. Note that this name
    is not unique: two distinct variables may have the same name. *)
let base_name : var -> string = fun (_i,n) -> n

(** [uniq_name x] returns a string uniquely identifying the variable [x]. *)
let uniq_name : var -> string = fun (i,_) -> "v" ^ string_of_int i

(** Sets and maps of variables. *)
module Var = struct
  type t = var
  let compare = compare_vars
end

module VarSet = Set.Make(Var)
module VarMap = Map.Make(Var)

(* Type for bound variables. [InSub i] refers to the i-th slot in the
   substitution of the parent binder, [InEnv i] refers to the i-th slot in
   the closure environment of the parent binder (variables bound by a binder
   which is not the direct parent). *)
type bvar = InSub of int | InEnv of int

(** The priority of an infix operator is a floating-point number. *)
type priority = float

(** Notations. *)
type 'a notation =
  | NoNotation
  | Prefix of 'a
  | Postfix of 'a
  | Infix of Pratter.associativity * 'a
  | Zero
  | Succ of 'a notation (* NoNotation, Prefix or Postfix only *)
  | Quant
  | PosOne
  | PosDouble
  | PosSuccDouble
  | IntZero
  | IntPos
  | IntNeg

(** Representation of a term (or types) in a general sense. Values of the type
    are also used, for example, in the representation of patterns or rewriting
    rules. Specific constructors are included for such applications,  and they
    are considered invalid in unrelated code.

    Bound variables [Bvar] never appear outside of the current module. They
    correspond to the variables bound by a binder above. They are replaced by
    [Vari] whenever the binder is destructed (via unbind and the like)
 *)
type term =
  | Vari of var (** Free variable. *)
  | Bvar of bvar (** Bound variables. Only used internally. *)
  | Type (** "TYPE" constant. *)
  | Kind (** "KIND" constant. *)
  | Symb of sym (** User-defined symbol. *)
  | Prod of term * binder (** Dependent product. *)
  | Abst of term * binder (** Abstraction. *)
  | Appl of term * term (** Term application. *)
  | Meta of meta * term array (** Metavariable application. *)
  | Patt of int option * string * term array
  (** Pattern variable application (only used in rewriting rules). *)
  | Wild (** Wildcard (only used for surface matching, never in LHS). *)
  | Plac of bool
  (** [Plac b] is a placeholder, or hole, for not given terms. Boolean [b] is
      true if the placeholder stands for a type. *)
  | TRef of term option Timed.ref
  (** Reference cell (used in surface matching, and evaluation with
      sharing). *)
  | LLet of term * term * binder
  (** [LLet(a, t, u)] is [let x : a ≔ t in u] (with [x] bound in [u]). *)

(** Type for binders, implemented as closures. The bound variables of a
    closure term always refer either to a variable bound by the parent binder
    or to a slot in the closure environment of the parent binder. No direct
    reference to variables bound by an ancestor binder!

    In a binder [(bi,u,e)] of arity [n], [Bvar(InSub i)] occurring in the
    closure term [u] (with [i < n]) refers to the bound variable at position
    [i] in the given substitution (e.g. argument [vs] of msubst), and
    [Bvar(InEnv i)] refers to the term [e.(i)]

    For instance, the term [λx. λy. x y] is represented as
    [Abst(_,(_,Abst(_,(_,Appl(Bvar(InSub 0)|Bvar(InEnv 0)),
                       [|Bvar(InSub 0)|])),
             [||]))]
 *)
and binder = binder_info * term * term array
and mbinder = mbinder_info * term * term array

(** {b NOTE} that a wildcard "_" of the concrete (source code) syntax may have
    a different representation depending on the context. For instance, the
    {!constructor:Wild} constructor is only used when matching patterns (e.g.,
    with the "rewrite" tactic). In the LHS of a rewriting {!type:rule}, we use
    the {!constructor:Patt} constructor to represend wildcards of the concrete
    syntax. They are thus considered to be fresh, unused pattern variables. *)

(** Representation of a decision tree (used for rewriting). *)
and dtree = rule Tree_type.dtree

(** Representation of a user-defined symbol. *)
and sym =
  { sym_expo  : expo (** Visibility. *)
  ; sym_path  : Path.t (** Module in which the symbol is defined. *)
  ; sym_name  : string (** Name. *)
  ; sym_type  : term Timed.ref (** Type. *)
  ; sym_impl  : bool list (** Implicit arguments ([true] meaning implicit). *)
  ; sym_prop  : prop (** Property. *)
  ; sym_not   : float notation Timed.ref (** Notation. *)
  ; sym_def   : term option Timed.ref (** Definition with ≔. *)
  ; sym_opaq  : bool Timed.ref (** Opacity. *)
  ; sym_rules : rule list Timed.ref (** Rewriting rules. *)
  ; sym_mstrat: match_strat (** Matching strategy. *)
  ; sym_dtree : dtree Timed.ref (** Decision tree used for matching. *)
  ; sym_pos   : Pos.popt (** Position in source file of symbol name. *)
  ; sym_decl_pos : Pos.popt (** Position in source file of symbol declaration
                                without its definition. *) }

(** {b NOTE} {!field:sym_type} holds a (timed) reference for a  technical
    reason related to the writing of signatures as binary files  (in  relation
    to {!val:Sign.link} and {!val:Sign.unlink}).  This is necessary to
    ensure that two identical symbols are always physically equal, even across
    signatures. It should NOT be otherwise mutated. *)

(** {b NOTE} We maintain the invariant that {!field:sym_impl} never ends  with
    [false]. Indeed, this information would be redundant. If a symbol has more
    arguments than there are booleans in the list then the extra arguments are
    all explicit. Finally, note that {!field:sym_impl} is empty if and only if
    the symbol has no implicit parameters. *)

(** {b NOTE} {!field:sym_prop} restricts the possible
    values of {!field:sym_def} and {!field:sym_rules} fields. A symbol is
    not allowed to be given rewriting rules (or a definition) when its mode is
    set to {!constructor:Constant}. Moreover, a symbol should not be given at
    the same time a definition (i.e., {!field:sym_def} different from [None])
    and rewriting rules (i.e., {!field:sym_rules} is non-empty). *)

(** {b NOTE} For generated symbols (recursors, axioms), {!field:sym_pos} may
   not be valid positions in the source. These virtual positions are however
   important for exporting lambdapi files to other formats. *)

(** {3 Representation of rewriting rules} *)

(** Representation of a rewriting rule. A rewriting rule is mainly formed of a
    LHS (left hand side),  which is the pattern that should be matched for the
    rule to apply, and a RHS (right hand side) giving the action to perform if
    the rule applies. More explanations are given below. *)
 and rule =
  { lhs      : term list (** Left hand side (LHS). *)
  ; rhs      : term (** Right hand side (RHS). *)
  ; arity    : int (** Required number of arguments to be applicable. *)
  ; arities  : int array
  (** Arities of the pattern variables bound in the RHS. *)
  ; vars_nb  : int (** Number of variables in [lhs]. *)
  ; xvars_nb : int (** Number of variables in [rhs] but not in [lhs]. *)
  ; rule_pos : Pos.popt (** Position of the rule in the source file. *) }

(** {b NOTE} {!field:arity} gives the number of arguments contained in the
   LHS. It is always equal to [List.length r.lhs] and gives the minimal number
   of arguments required to match the LHS. *)

(** {b NOTE} For generated rules, {!field:rule_pos} may not be valid positions
   in the source. These virtual positions are however important for exporting
   lambdapi files to other formats. *)

(** All variables of rewriting rules that appear in the RHS must appear in the
   LHS. In the case of unification rules, we allow variables to appear only in
   the RHS. In that case, these variables are replaced by fresh meta-variables
   each time the rule is used. *)

(** During evaluation, we only try to apply rewriting rules when we reduce the
   application of a symbol [s] to a list of argument [ts]. At this point, the
   symbol [s] contains every rule [r] that can potentially be applied in its
   {!field:sym_rules} field. To check if a rule [r] applies, we match the
   elements of [r.lhs] with those of [ts] while building an environment [env].
   During this process, a pattern of
   the form {!constructor:Patt}[(Some i,_,_)] matched against a term [u] will
   results in [env.(i)] being set to [u]. If all terms of [ts] can be matched
   against corresponding patterns, then environment [env] is fully constructed
   and it can hence be substituted in [r.rhs] with [subst_patt env r.rhs]
   to get the result of the application of the rule. *)

(** {3 Metavariables and related functions} *)

(** Representation of a metavariable,  which corresponds to a yet unknown
    term typable in some context. The substitution of the free variables
    of the context is suspended until the metavariable is instantiated
    (i.e., set to a particular term).  When a metavariable [m] is
    instantiated,  the suspended substitution is  unlocked and terms of
    the form {!constructor:Meta}[(m,env)] can be unfolded. *)
and meta =
  { meta_key   : int (** Unique key. *)
  ; meta_type  : term Timed.ref (** Type. *)
  ; meta_arity : int (** Arity (environment size). *)
  ; meta_value : mbinder option Timed.ref (** Definition. *) }


let binder_name : binder -> string = fun (bi,_,_) -> bi.binder_name
let mbinder_names : mbinder -> string array = fun (bi,_,_) -> bi.mbinder_name

(** [mbinder_arity b] gives the arity of the [mbinder]. *)
let mbinder_arity : mbinder -> int =
  fun (i,_,_) -> Array.length i.mbinder_name

(** [binder_occur b] tests whether the bound variable occurs in [b]. *)
let binder_occur : binder -> bool = fun (bi,_,_) -> bi.binder_bound
let mbinder_occur : mbinder -> int -> bool =
  fun (bi,_,_) i -> assert (i < Array.length bi.mbinder_name);
                    bi.mbinder_bound.(i)

(** Minimize [impl] to enforce our invariant (see {!type:Terms.sym}). *)
let minimize_impl : bool list -> bool list =
  let rec rem_false l = match l with false::l -> rem_false l | _ -> l in
  fun l -> List.rev (rem_false (List.rev l))

(** [create_sym path expo prop mstrat opaq name pos typ impl] creates a new
    symbol with path [path], exposition [expo], property [prop], opacity
    [opaq], matching strategy [mstrat], name [name.elt], type [typ], implicit
    arguments [impl], position [name.pos], declaration position [pos], no
    definition and no rules. *)
let create_sym : Path.t -> expo -> prop -> match_strat -> bool ->
  Pos.strloc -> Pos.popt -> term -> bool list -> sym =
  fun sym_path sym_expo sym_prop sym_mstrat sym_opaq
    { elt = sym_name; pos = sym_pos } sym_decl_pos typ sym_impl ->
  let open Timed in
  {sym_path; sym_name; sym_type = ref typ; sym_impl; sym_def = ref None;
   sym_opaq = ref sym_opaq; sym_rules = ref []; sym_not = ref NoNotation;
   sym_dtree = ref Tree_type.empty_dtree;
   sym_mstrat; sym_prop; sym_expo; sym_pos ; sym_decl_pos }

(** [is_constant s] tells whether [s] is a constant. *)
let is_constant : sym -> bool = fun s -> s.sym_prop = Const

(** [is_injective s] tells whether [s] is injective, which is in partiular the
   case if [s] is constant. *)
let is_injective : sym -> bool = fun s ->
  match s.sym_prop with Const | Injec -> true | _ -> Timed.(!(s.sym_opaq))

(** [is_private s] tells whether the symbol [s] is private. *)
let is_private : sym -> bool = fun s -> s.sym_expo = Privat

(** [is_modulo s] tells whether the symbol [s] is modulo some equations. *)
let is_modulo : sym -> bool = fun s ->
  match s.sym_prop with Commu | AC _ -> true | _ -> false
let is_ac : sym -> bool = fun s ->
  match s.sym_prop with AC _ -> true | _ -> false

(** Sets and maps of symbols. *)
module Sym = struct
  type t = sym
  let compare s1 s2 =
    if s1 == s2 then 0 else
    match Stdlib.compare s1.sym_name s2.sym_name with
    | 0 -> Stdlib.compare s1.sym_path s2.sym_path
    | n -> n
end

module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)

(** [is_unset m] returns [true] if [m] is not instantiated. *)
let is_unset : meta -> bool = fun m -> Timed.(!(m.meta_value)) = None

(** Sets and maps of metavariables. *)
module Meta = struct
  type t = meta
  let compare m1 m2 = m2.meta_key - m1.meta_key
end

module MetaSet = Set.Make(Meta)
module MetaMap = Map.Make(Meta)

(** [add_args t args] builds the application of the {!type:term} [t] to a list
    arguments [args]. When [args] is empty, the returned value is (physically)
    equal to [t]. *)
let add_args : term -> term list -> term =
  List.fold_left (fun t u -> Appl(t,u))

(** [add_args_map f t ts] is equivalent to [add_args t (List.map f ts)] but
   more efficient. *)
let add_args_map : term -> (term -> term) -> term list -> term = fun t f ts ->
  List.fold_left (fun t u -> Appl(t, f u)) t ts

(** Printing functions for debug. *)
let rec term : term pp = fun ppf t ->
  match unfold t with
  | Bvar (InSub k) -> out ppf "`%d" k
  | Bvar (InEnv k) -> out ppf "~%d" k
  | Vari v -> var ppf v
  | Type -> out ppf "TYPE"
  | Kind -> out ppf "KIND"
  | Symb s -> sym ppf s
  | Prod(a,(n,b,e)) ->
      out ppf "(Π %s: %a, %a#(%a))" n.binder_name term a clos_env e term b
  | Abst(a,(n,b,e)) ->
      out ppf "(λ %s: %a, %a#(%a))" n.binder_name term a clos_env e term b
  | Appl(a,b) -> out ppf "(%a %a)" term a term b
  | Meta(m,ts) -> out ppf "?%d%a" m.meta_key terms ts
  | Patt(i,s,ts) -> out ppf "$%a_%s%a" (D.option D.int) i s terms ts
  | Plac(_) -> out ppf "_"
  | Wild -> out ppf "_"
  | TRef r -> out ppf "&%a" (Option.pp term) Timed.(!r)
  | LLet(a,t,(n,b,e)) ->
      out ppf "let %s : %a ≔ %a in %a#(%a)"
        n.binder_name term a term t clos_env e term b
and var : var pp = fun ppf (i,n) -> out ppf "%s%d" n i
and sym : sym pp = fun ppf s -> string ppf s.sym_name
and terms : term array pp = fun ppf ts ->
  if Array.length ts > 0 then D.array term ppf ts
and clos_env : term array pp =  fun ppf env -> D.array term ppf env

(** [unfold t] repeatedly unfolds the definition of the surface constructor
   of [t], until a significant {!type:term} constructor is found.  The term
   that is returned can be neither an instantiated metavariable
   nor a reference cell ({!constructor:TRef} constructor). Note
   that the returned value is physically equal to [t] if no unfolding was
   performed. {b NOTE} that {!val:unfold} must (almost) always be called
   before matching over a value of type {!type:term}. *)
and unfold : term -> term = fun t ->
  match t with
  | Meta(m, ts) ->
      begin
        match Timed.(!(m.meta_value)) with
        | None    -> t
        | Some(b) -> unfold (msubst b ts)
      end
  | TRef(r) ->
      begin
        match Timed.(!r) with
        | None    -> t
        | Some(v) -> unfold v
      end
  | _ -> t

(** [msubst b vs] substitutes the variables bound by [b] with the values
    [vs].  Note that the length of the [vs] array should match the arity of
    the multiple binder [b]. *)
and msubst : mbinder -> term array -> term = fun (bi,tm,env) vs ->
  let n = Array.length bi.mbinder_name in
  assert (Array.length vs = n);
  let rec msubst t =
    (*if Logger.log_enabled() then
      log "msubst %a %a" (D.array term) vs term t;*)
    match unfold t with
    | Bvar (InSub p) -> assert bi.mbinder_bound.(p); vs.(p)
    | Bvar (InEnv p) -> env.(p)
    | Appl(a,b) -> Appl(msubst a, msubst b)
    (* No need to substitute in the closure term: all bound variables appear
       in the closure environment *)
    | Abst(a,(n,u,e)) -> Abst(msubst a, (n, u, Array.map msubst e))
    | Prod(a,(n,u,e)) -> Prod(msubst a, (n, u, Array.map msubst e))
    | LLet(a,t,(n,u,e)) ->
        LLet(msubst a, msubst t, (n, u, Array.map msubst e))
    | Meta(m,ts) -> Meta(m, Array.map msubst ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map msubst ts)
    | Type | Kind | Vari _ | Wild | Symb _ | Plac _ | TRef _ -> t
  in
  let r =
    if Array.for_all ((=) false) bi.mbinder_bound && Array.length env = 0
    then tm
    else msubst tm in
  (*if Logger.log_enabled() then
  log "msubst %a#%a %a = %a" clos_env env term tm (D.array term) vs term r;*)
  r

(** [get_args t] decomposes the {!type:term} [t] into a pair [(h,args)], where
    [h] is the head term of [t] and [args] is the list of arguments applied to
    [h] in [t]. The returned [h] cannot be an [Appl] node. *)
let get_args : term -> term * term list = fun t ->
  let rec get_args t acc =
    match unfold t with
    | Appl(t,u) -> get_args t (u::acc)
    | t         -> t, acc
  in get_args t []

(** [get_args_len t] is similar to [get_args t] but it also returns the length
    of the list of arguments. *)
let get_args_len : term -> term * term list * int = fun t ->
  let rec get_args_len acc len t =
    match unfold t with
    | Appl(t, u) -> get_args_len (u::acc) (len + 1) t
    | t          -> (t, acc, len)
  in
  get_args_len [] 0 t

(** Total order on terms. *)
let rec cmp : term cmp = fun t t' ->
  match unfold t, unfold t' with
  | Vari x, Vari x' -> compare_vars x x'
  | Type, Type
  | Kind, Kind
  | Wild, Wild -> 0
  | Symb s, Symb s' -> Sym.compare s s'
  | Prod(t,u), Prod(t',u')
  | Abst(t,u), Abst(t',u') -> lex cmp cmp_binder (t,u) (t',u')
  | Appl(t,u), Appl(t',u') -> lex cmp cmp (u,t) (u',t')
  | Meta(m,ts), Meta(m',ts') ->
      lex Meta.compare (Array.cmp cmp) (m,ts) (m',ts')
  | Patt(i,s,ts), Patt(i',s',ts') ->
    lex3 Stdlib.compare Stdlib.compare (Array.cmp cmp) (i,s,ts) (i',s',ts')
  | Bvar i, Bvar j -> Stdlib.compare i j
  | TRef r, TRef r' -> Stdlib.compare r r'
  | LLet(a,t,u), LLet(a',t',u') -> lex3 cmp cmp cmp_binder (a,t,u) (a',t',u')
  | t, t' -> cmp_tag t t'

and cmp_binder : binder cmp =
(*  fun ({binder_name;binder_bound},u,e) (bi',u',e') ->
  let mbi = {mbinder_name=[|binder_name|];mbinder_bound=[|binder_bound|]} in
  let var = Vari(new_var binder_name) in
  cmp (msubst (mbi,u,e)[|var|])
    (msubst({mbi with mbinder_bound=[|bi'.binder_bound|]},u',e')[|var|])*)
  fun (_,u,e) (_,u',e') -> lex cmp (Array.cmp cmp) (u,e) (u',e')

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
let is_symb : sym -> term -> bool = fun s t ->
  match unfold t with Symb(r) -> r == s | _ -> false

(** [is_abst t] returns [true] iff [t] is of the form [Abst(_)]. *)
let is_abst : term -> bool = fun t ->
  match unfold t with Abst(_) -> true | _ -> false

(** [is_prod t] returns [true] iff [t] is of the form [Prod(_)]. *)
let is_prod : term -> bool = fun t ->
  (match unfold t with Prod(_) -> true | _ -> false)

(** [iter_atoms db f g t] applies f to every occurrence of a variable in t,
    g to every occurrence of a symbol, and db to every occurrence of a
    bound variable.
    We have to be careful with binders since in the current implementation
    closure environment may contain slots for variables that don't actually
    appear. This is done by first checking the closure term, recording which
    bound variables actually occur, and then check the elements of the
    closure environment which occur.
 *)
let rec iter_atoms :
          (bvar -> unit) -> (var -> unit) -> (sym -> unit) -> term -> unit =
  fun db f g t ->
  let rec check db t =
    match unfold t with
    | Vari x -> f x
    | Symb s -> g s
    | Bvar i -> db i
    | Appl(a,b) -> check db a; check db b
    | Abst(a,b)
    | Prod(a,b) -> check db a; check_binder db b
    | LLet(a,t,b) -> check db a; check db t; check_binder db b
    | Meta(_,ts)
    | Patt(_,_,ts) -> Array.iter (check db) ts
    | _ -> ()
  and check_binder db (_bi,u,env) =
    iter_atoms_closure db f g u env in
  check db t

and iter_atoms_closure :
      (bvar -> unit) -> (var -> unit) -> (sym -> unit) -> term -> term array
      -> unit =
  fun db f g u env ->
  (* env positions occuring in [u] *)
  let u_pos = ref IntSet.empty in
  let db_u db =
    match db with
    | InEnv p -> u_pos := IntSet.add p !u_pos
    | _ -> () in
  (* We iterate on u, recording which env positions occur *)
  iter_atoms db_u f g u;
  (* We then iterate on the members of [e] that *actually* occur in u *)
  Array.iteri (fun i t ->
      if IntSet.mem i !u_pos then iter_atoms db f g t
    (*else if t <> Wild then env.(i) <- Wild*) )
    env

let iter_atoms_mbinder
    : (bvar -> unit) -> (var -> unit) -> (sym -> unit) -> mbinder -> unit =
  fun db f g (_bi,u,env) -> iter_atoms_closure db f g u env

(** [occur x t] tells whether variable [x] occurs in [t]. *)
let occur : var -> term -> bool =
  fun x t ->
  try iter_atoms
        (fun _ -> ())
        (fun y -> if x==y then raise Exit)
        (fun _-> ()) t;
      false
  with Exit -> true

let occur_mbinder : var -> mbinder -> bool =
  fun x b ->
  try iter_atoms_mbinder
        (fun _ -> ())
        (fun y -> if x==y then raise Exit)
        (fun _-> ()) b;
      false
  with Exit -> true

(** [is_closed t] checks whether [t] is closed (w.r.t. variables).  We have to
    be careful with binders since in the current implementation closure
    environment may contain slots for variables that don't actually appear *)
let is_closed : term -> bool =
  fun t ->
  try iter_atoms (fun _ -> ()) (fun _ -> raise Exit) (fun _ -> ()) t; true
  with Exit -> false

let is_closed_mbinder : mbinder -> bool =
  fun b ->
  try iter_atoms_mbinder
        (fun _ -> ()) (fun _ -> raise Exit) (fun _ -> ()) b; true
  with Exit -> false

(** [subst b v] substitutes the variable bound by [b] with the value [v].
    Assumes v is closed (since only called from outside the term library. *)
let subst : binder -> term -> term = fun (bi,tm,env) v ->
  let rec subst t =
    match unfold t with
    | Bvar (InSub _) -> assert bi.binder_bound; v
    | Bvar (InEnv p) -> env.(p)
    | Appl(a,b) -> Appl(subst a, subst b)
    | Abst(a,(n,u,e)) -> Abst(subst a, (n, u, Array.map subst e))
    | Prod(a,(n,u,e)) -> Prod(subst a, (n ,u, Array.map subst e))
    | LLet(a,t,(n,u,e)) -> LLet(subst a, subst t, (n, u, Array.map subst e))
    | Meta(m,ts) -> Meta(m, Array.map subst ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map subst ts)
    | _ -> t
  in
  let r =
    if bi.binder_bound = false &&  Array.length env = 0 then tm
    else subst tm in
  if Logger.log_enabled() then
    log "subst %a#%a [%a] = %a" clos_env env term tm term v term r;
  r

(** [unbind b] substitutes the binder [b] by a fresh variable of name [name]
   if given, or the binder name otherwise. The variable and the result of the
   substitution are returned. *)
let unbind : ?name:string -> binder -> var * term =
  fun ?(name="") ((bn,_,_) as b) ->
  let n = if name="" then bn.binder_name else name in
  let x = new_var n in x, subst b (Vari x)

(** [unbind2 f g] is similar to [unbind f], but it substitutes two binders [f]
   and [g] at once using the same fresh variable. *)
let unbind2 : ?name:string -> binder -> binder -> var * term * term =
  fun ?(name="") ((bn1,_,_) as b1) b2 ->
  let n = if name="" then bn1.binder_name else name in
  let x = new_var n in x, subst b1 (Vari x), subst b2 (Vari x)

(** [unmbind b] substitutes the multiple binder [b] with fresh variables. This
    function is analogous to [unbind] for binders. Note that the names used to
    create the fresh variables are based on those of the multiple binder. *)
let unmbind : mbinder -> var array * term =
  fun (({mbinder_name=names;_},_,_) as b) ->
  let xs = Array.init (Array.length names) (fun i -> new_var names.(i)) in
  xs, msubst b (Array.map (fun x -> Vari x) xs)

(** [bind_var x t] binds the variable [x] in [t], producing a binder. *)
let bind_var  : var -> term -> binder = fun ((_,n) as x) t ->
  let bound = Stdlib.ref false in
  (* Replace variables [x] by de Bruijn index [i] *)
  let rec bind i t =
    (*if Logger.log_enabled() then log "bind_var %d %a" i term t;*)
    match unfold t with
    | Vari y when y == x -> bound := true; Bvar i
    | Appl(a,b) ->
        let a' = bind i a in
        let b' = bind i b in
        if a==a' && b==b' then t else Appl(a', b')
    (* No need to call Appl here as we only replace free variables by de
       Bruijn indices. *)
    | Abst(a,b) ->
        let a' = bind i a in
        let b' = bind_binder i b in
        if a==a' && b==b' then t else Abst(a', b')
    | Prod(a,b) ->
        let a' = bind i a in
        let b' = bind_binder i b in
        if a==a' && b==b' then t else Prod(a', b')
    | LLet(a,m,b) ->
        let a' = bind i a in
        let m' = bind i m in
        let b' = bind_binder i b in
        if a==a' && m==m' && b==b' then t else LLet(a', m', b')
    | Meta(m,ts) ->
        let ts' = Array.map (bind i) ts in
        if Array.for_all2 (==) ts ts' then t else Meta(m, ts')
    | Patt(j,n,ts) ->
        let ts' = Array.map (bind i) ts in
        if Array.for_all2 (==) ts ts' then t else Patt(j,n,ts')
    | _ -> t

  and bind_binder i (bi,u,env as b) =
    let env' = Array.map (bind i) env in
    let j = InEnv (Array.length env') in
    let u' = bind j u in
    if u==u' then (* If [u==u'] then x does not occur in u *)
      if Array.for_all2 (==) env env' then b
      else (bi, u', env')
    else (* x occurs, it has been replaced by [Bvar(j)],
            corresponding to the head of [e] *)
      (bi, u', Array.append env' [|Bvar i|]) in

  let b = bind (InSub 0) t in
  if Logger.log_enabled() then
    log "bind_var %a %a = %a" var x term t term b;
  {binder_name=n; binder_bound= !bound}, b, [||]

(** Build a non-dependent product. *)
let mk_Arro (a,b) = let x = new_var "_" in Prod(a, bind_var x b)

(** Curryfied versions of some constructors. *)
let mk_Vari v = Vari v
let mk_Abst (a,b) = Abst (a,b)
let mk_Prod (a,b) = Prod (a,b)

(** [binder f b] applies f inside [b]. *)
let binder : (term -> term) -> binder -> binder = fun f b ->
  let x,t = unbind b in bind_var x (f t)

(** [bind_mvar xs t] binds the variables of [xs] in [t] to get a binder.
    It is the equivalent of [bind_var] for multiple variables. *)
let bind_mvar : var array -> term -> mbinder =
  let empty = {mbinder_name=[||]; mbinder_bound=[||]} in
  fun xs tm ->
  if Array.length xs = 0 then empty, tm, [||] else begin
  (*if Logger.log_enabled() then
    log "bind_mvar %a" (D.array var) xs;*)
  let top_map = Stdlib.ref IntMap.empty
  and mbinder_bound = Array.make (Array.length xs) false in
  Array.iteri
    (fun i (ki,_) -> Stdlib.(top_map := IntMap.add ki i !top_map)) xs;
  let top_fvar key =
    let p = Stdlib.(IntMap.find key !top_map) in
    mbinder_bound.(p) <- true; Bvar (InSub p) in
  (* Replace variables [x] in [xs] by de Bruijn index [fvar x] *)
  let rec bind fvar t =
    (*if Logger.log_enabled() then log "bind_mvar %d %a" i term t;*)
    match unfold t with
    | Vari (key,_) ->
        if Stdlib.(IntMap.mem key !top_map) then fvar key else t
    | Appl(a,b) ->
        let a' = bind fvar a in
        let b' = bind fvar b in
        if a==a' && b==b' then t else Appl(a', b')
    (* No need to call Appl here as we only replace free variables by de
       Bruijn indices. *)
    | Abst(a,b) ->
        let a' = bind fvar a in
        let b' = bind_binder fvar b in
        if a==a' && b==b' then t else Abst(a', b')
    | Prod(a,b) ->
        let a' = bind fvar a in
        let b' = bind_binder fvar b in
        if a==a' && b==b' then t else Prod(a', b')
    | LLet(a,m,b) ->
        let a' = bind fvar a in
        let m' = bind fvar m in
        let b' = bind_binder fvar b in
        if a==a' && m==m' && b==b' then t else LLet(a', m', b')
    | Meta(m,ts) ->
        let ts' = Array.map (bind fvar) ts in
        if Array.for_all2 (==) ts ts' then t else Meta(m, ts')
    | Patt(j,n,ts) ->
        let ts' = Array.map (bind fvar) ts in
        if Array.for_all2 (==) ts ts' then t else Patt(j,n,ts')
    | _ -> t

  and bind_binder fvar (bi,u,u_env as b) =
    let open Stdlib in
    let u_env' = Array.map (bind fvar) u_env in
    let u_n = ref 0 in
    let u_map = ref IntMap.empty in
    let fvar' key =
      match IntMap.find_opt key !u_map with
      | Some p -> Bvar (InEnv p)
      | None ->
          let p' = Array.length u_env' + !u_n in
          incr u_n;
          u_map := IntMap.add key p' !u_map;
          Bvar (InEnv p') in
    let u' = bind fvar' u in
    if u==u' && !u_n = 0 && Lplib.Array.for_all2 (==) u_env u_env' then b
    else (* some vars of [xs] occur in u *)
      let u_env' = Array.append u_env' (Array.make !u_n Wild) in
      IntMap.iter (fun key p -> u_env'.(p) <- fvar key) !u_map;
      (bi, u', u_env') in

  let b = bind top_fvar tm in
  if Logger.log_enabled() then
    log "bind_mvar %a %a = %a %a"
      (D.array var) xs term tm pr_bound mbinder_bound term b;
  let bi = { mbinder_name = Array.map base_name xs; mbinder_bound } in
  bi, b, [||]
  end

(** Patt substitution. *)
let subst_patt : mbinder option array -> term -> term = fun env ->
  let rec subst_patt t =
    match unfold t with
    | Patt(Some i,n,ts) when 0 <= i && i < Array.length env ->
      begin match env.(i) with
      | Some b -> msubst b (Array.map subst_patt ts)
      | None -> Patt(Some i,n,Array.map subst_patt ts)
      end
    | Patt(i,n,ts) -> Patt(i, n, Array.map subst_patt ts)
    | Prod(a,(n,b,e)) ->
        Prod(subst_patt a, (n, subst_patt b, Array.map subst_patt e))
    | Abst(a,(n,b,e)) ->
        Abst(subst_patt a, (n, subst_patt b, Array.map subst_patt e))
    | Appl(a,b) -> Appl(subst_patt a, subst_patt b)
    | Meta(m,ts) -> Meta(m, Array.map subst_patt ts)
    | LLet(a,t,(n,b,e)) ->
        LLet(subst_patt a, subst_patt t,
                (n, subst_patt b, Array.map subst_patt e))
    | Wild
    | Plac _
    | TRef _
    | Bvar _
    | Vari _
    | Type
    | Kind
    | Symb _ -> t
  in subst_patt

(** [cleanup t] unfold all metas and TRef's in [t]. *)
let rec cleanup : term -> term = fun t ->
  match unfold t with
  | Patt(i,n,ts) -> Patt(i, n, Array.map cleanup ts)
  | Prod(a,b) -> Prod(cleanup a, binder cleanup b)
  | Abst(a,b) -> Abst(cleanup a, binder cleanup b)
  | Appl(a,b) -> Appl(cleanup a, cleanup b)
  | Meta(m,ts) -> Meta(m, Array.map cleanup ts)
  | LLet(a,t,b) -> LLet(cleanup a, cleanup t, binder cleanup b)
  | Wild -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | Bvar _ -> assert false
  | Vari _
  | Type
  | Kind
  | Symb _ -> t

(** Type of a symbol and a rule. *)
type sym_rule = sym * rule

let lhs : sym_rule -> term = fun (s, r) -> add_args (Symb s) r.lhs
let rhs : sym_rule -> term = fun (_, r) -> r.rhs

(** Positions in terms in reverse order. The i-th argument of a constructor
   has position i-1. *)
type subterm_pos = int list

let subterm_pos : subterm_pos pp = fun ppf l -> D.(list int) ppf (List.rev l)

(** Type of critical pair positions (pos,l,r,p,l_p). *)
type cp_pos = Pos.popt * term * term * subterm_pos * term

(** Typing context associating a variable to a type and possibly a
    definition. The typing environment [x1:A1,..,xn:An] is represented by the
    list [xn:An;..;x1:A1] in reverse order (last added variable comes
    first). *)
type ctxt = (var * term * term option) list

let decl ppf (v,a,d) =
  out ppf "%a: %a" var v term a;
  match d with
  | None -> ()
  | Some d -> out ppf " ≔ %a" term d

let ctxt : ctxt pp = fun ppf c -> List.pp decl ", " ppf (List.rev c)

(** Type of unification constraints. *)
type constr = ctxt * term * term

(** Representation of unification problems. *)
type problem_aux =
  { to_solve  : constr list
  (** List of unification problems to solve. *)
  ; unsolved  : constr list
  (** List of unification problems that could not be solved. *)
  ; recompute : bool
  (** Indicates whether unsolved problems should be rechecked. *)
  ; metas : MetaSet.t
  (** Set of unsolved metas. *) }

type problem = problem_aux Timed.ref

(** Create a new empty problem. *)
let new_problem : unit -> problem = fun () ->
  Timed.ref
    {to_solve  = []; unsolved = []; recompute = false; metas = MetaSet.empty}

(** Printing functions for debug. *)
module Raw = struct
  let sym = sym let _ = sym
  let term = term let _ = term
  let ctxt = ctxt let _ = ctxt
end
