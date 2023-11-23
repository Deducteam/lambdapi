(** Internal representation of terms.

   This module contains the definition of the internal representation of
   terms, together with smart constructors and low level operation. The
   representation strongly relies on the {!module:Bindlib} library, which
   provides a convenient abstraction to work with binders.

    @see <https://rlepigre.github.io/ocaml-bindlib/> *)

open Timed
open Lplib open Base
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

(** Symbol properties. *)
type prop =
  | Defin (** Definable. *)
  | Const (** Constant. *)
  | Injec (** Injective. *)
  | Commu (** Commutative. *)
  | Assoc of bool (** Associative left if [true], right if [false]. *)
  | AC of bool (** Associative and commutative. *)

(** Representation of a term (or types) in a general sense. Values of the type
    are also used, for example, in the representation of patterns or rewriting
    rules. Specific constructors are included for such applications,  and they
    are considered invalid in unrelated code. *)
type term =
  | Vari of tvar (** Free variable. *)
  | Type (** "TYPE" constant. *)
  | Kind (** "KIND" constant. *)
  | Symb of sym (** User-defined symbol. *)
  | Prod of term * tbinder (** Dependent product. *)
  | Abst of term * tbinder (** Abstraction. *)
  | Appl of term * term (** Term application. *)
  | Meta of meta * term array (** Metavariable application. *)
  | Patt of int option * string * term array
  (** Pattern variable application (only used in rewriting rules LHS). *)
  | TEnv of term_env * term array
  (** Term environment (only used in rewriting rules RHS). *)
  | Wild (** Wildcard (only used for surface matching, never in LHS). *)
  | Plac of bool
  (** [Plac b] is a placeholder, or hole, for not given terms. Boolean [b] is
      true if the placeholder stands for a type. *)
  | TRef of term option ref (** Reference cell (used in surface matching). *)
  | LLet of term * term * tbinder
  (** [LLet(a, t, u)] is [let x : a ≔ t in u] (with [x] bound in [u]). *)

(** {b NOTE} that a wildcard "_" of the concrete (source code) syntax may have
    a different representation depending on the application. For instance, the
    {!constructor:Wild} constructor is only used when matching patterns (e.g.,
    with the "rewrite" tactic). In the LHS of a rewriting {!type:rule}, we use
    the {!constructor:Patt} constructor to represend wildcards of the concrete
    syntax. They are thus considered to be fresh, unused pattern variables. *)

(** Representation of a rewriting rule RHS (or action) as given in the type of
    rewriting rules (see {!field:Term.rhs}) with the number of variables that
    are not in the LHS. In decision trees, a RHS is stored in every leaf since
    they correspond to matched rules. *)
and rhs = (term_env, term) Bindlib.mbinder

(** Representation of a decision tree (used for rewriting). *)
and dtree = (rhs * int) Tree_type.dtree

(** Representation of a user-defined symbol. Symbols carry a "mode" indicating
    whether they may be given rewriting rules or a definition. Invariants must
    be enforced for "mode" consistency (see {!type:sym_prop}).  *)
and sym =
  { sym_expo  : expo (** Visibility. *)
  ; sym_path  : Path.t (** Module in which the symbol is defined. *)
  ; sym_name  : string (** Name. *)
  ; sym_type  : term ref (** Type. *)
  ; sym_impl  : bool list (** Implicit arguments ([true] meaning implicit). *)
  ; sym_prop  : prop (** Property. *)
  ; sym_def   : term option ref (** Definition with ≔. *)
  ; sym_opaq  : bool ref (** Opacity. *)
  ; sym_rules : rule list ref (** Rewriting rules. *)
  ; sym_mstrat: match_strat (** Matching strategy. *)
  ; sym_dtree : dtree ref (** Decision tree used for matching. *)
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
  ; rhs      : rhs (** Right hand side (RHS). *)
  ; arity    : int (** Required number of arguments to be applicable. *)
  ; arities  : int array
  (** Arities of the pattern variables bound in the RHS. *)
  ; vars     : tevar array
  (** Bindlib variables used to build [rhs]. The last [xvars_nb] variables
      appear only in [rhs]. *)
  ; xvars_nb : int (** Number of variables in [rhs] but not in [lhs]. *)
  ; rule_pos : Pos.popt (** Position of the rule in the source file. *) }

(** {b NOTE} The second parameter of {!constructor:Patt} holds an array of
   terms. This is essential for variables binding: using an array of variables
   would NOT suffice. *)

(** {b NOTE} {!field:arity} gives the number of arguments contained in the
   LHS. As a consequence, it is always equal to [List.length r.lhs] and it
   gives the minimal number of arguments required to match the LHS. *)

(** {b NOTE} For generated rules, {!field:rule_pos} may not be valid positions
   in the source. These virtual positions are however important for exporting
   lambdapi files to other formats. *)

(** The RHS (or action) or a rewriting rule is represented by a term, in which
    (higher-order) variables representing "terms with environments" (see the
    {!type:term_env} type) are bound. To effectively apply the rewriting rule,
    these  bound variables must be substituted using "terms with environments"
    that are constructed when matching the LHS of the rule. *)

(** All variables of rewriting rules that appear in the RHS must appear in the
    LHS. This constraint is checked in {!module:Sr}.In the case of unification
    rules, we allow variables to appear only in the RHS.  In that case, these
    variables are replaced by fresh meta-variables each time the rule is used.
    The last  {!field:terms.rule.xvars} variables of  {!field:terms.rule.vars}
    are such RHS-only variables. *)

(** Representation of a "term with environment", which intuitively corresponds
    to a term with bound variables (or a "higher-order" term) represented with
    the {!constructor:TE_Some} constructor. Other constructors are included so
    that "terms with environments" can be bound in the RHS of rewriting rules.
    This is purely technical. *)
 and term_env =
  | TE_Vari of tevar
  (** Free "term with environment" variable (used to build a RHS). *)
  | TE_Some of tmbinder
  (** Actual "term with environment" (used to instantiate a RHS). *)
  | TE_None
  (** Dummy term environment (used during matching). *)

(** The {!constructor:TEnv}[(te,env)] constructor intuitively corresponds to a
    term [te] with free variables together with an explicit environment [env].
    Note that the binding of the environment actually occurs in [te], when the
    constructor is of the form {!constructor:TE_Some}[(b)]. Indeed, [te] holds
    a multiple binder [b] that binds every free variables of the term at once.
    We then apply the substitution by performing a Bindlib substitution of [b]
    with the environment [env]. *)

(** During evaluation, we only try to apply rewriting rules when we reduce the
    application of a symbol [s] to a list of argument [ts]. At this point, the
    symbol [s] contains  every rule [r] that can potentially be applied in its
    {!field:sym_rules} field.  To check if a rule [r] applies,  we  match  the
    elements of [r.lhs] with those of [ts] while building an environment [env]
    of type {!type:term_env array}. During this process, a pattern of the form
    {!constructor:Patt}[(Some i,s,e)] matched against a term [u] will  results
    in [env.(i)] being set to [u]. If all terms of [ts] can be matched against
    corresponding patterns, then environment [env] is fully constructed and it
    can hence be substituted in [r.rhs] with [Bindlib.msubst r.rhs env] to get
    the result of the application of the rule. *)

(** {3 Metavariables and related functions} *)

(** Representation of a metavariable,  which corresponds to a yet unknown
    term typable in some context. The substitution of the free variables
    of the context is suspended until the metavariable is instantiated
    (i.e., set to a particular term).  When a metavariable [m] is
    instantiated,  the suspended substitution is  unlocked and terms of
    the form {!constructor:Meta}[(m,env)] can be unfolded. *)
 and meta =
  { meta_key   : int (** Unique key. *)
  ; meta_type  : term ref (** Type. *)
  ; meta_arity : int (** Arity (environment size). *)
  ; meta_value : tmbinder option ref (** Definition. *) }

and tbinder = (term, term) Bindlib.binder

and tmbinder = (term, term) Bindlib.mbinder

and tvar = term Bindlib.var

and tevar = term_env Bindlib.var

type tbox = term Bindlib.box

type tebox = term_env Bindlib.box

(** Minimize [impl] to enforce our invariant (see {!type:Terms.sym}). *)
let minimize_impl : bool list -> bool list =
  let rec rem_false l = match l with false::l -> rem_false l | _ -> l in
  fun l -> List.rev (rem_false (List.rev l))

(** Printing functions for debug. *)
module Raw = struct
let rec term : term pp = fun ppf t ->
  match t with
  | Vari v -> var ppf v
  | Type -> out ppf "TYPE"
  | Kind -> out ppf "KIND"
  | Symb s -> sym ppf s
  | Prod(a,b) ->
      if Bindlib.binder_constant b then
        let _, b = Bindlib.unbind b in out ppf "(%a → %a)" term a term b
      else out ppf "(Π %a)" binder (a,b)
  | Abst(a,b) -> out ppf "(λ %a)" binder (a,b)
  | Appl(a,b) -> out ppf "(%a %a)" term a term b
  | Meta(m,ts) -> out ppf "?%a%a" meta m terms ts
  | Patt(i,s,ts) -> out ppf "$%a_%s%a" (D.option D.int) i s terms ts
  | Plac(_) -> out ppf "_"
  | TEnv(te,ts) -> out ppf "<%a>%a" tenv te terms ts
  | Wild -> out ppf "_"
  | TRef r -> out ppf "&%a" (Option.pp term) !r
  | LLet(a,t,u) ->
      let x, u = Bindlib.unbind u in
      out ppf "let %a: %a ≔ %a in %a" var x term a term t term u
and terms : term array pp = fun ppf ts ->
  (*if Array.length ts > 0 then*) D.array term ppf ts
and var : tvar pp = fun ppf v -> out ppf "%s" (Bindlib.name_of v)
and binder : (term * tbinder) pp = fun ppf (a,b) ->
  let x, b = Bindlib.unbind b in
  out ppf "%a: %a, %a" var x term a term b
and meta : meta pp = fun ppf m ->
  out ppf "%d" m.meta_key
and sym : sym pp = fun ppf s -> out ppf "%s" s.sym_name
and tenv : term_env pp = fun ppf te ->
  match te with
  | TE_Vari v -> out ppf "%s" (Bindlib.name_of v)
  | TE_Some mb ->
    let vs, b = Bindlib.unmbind mb in
    out ppf "%a,%a" (D.array var) vs term b
  | TE_None -> ()
end

(** Typing context associating a [Bindlib] variable to a type and possibly a
    definition. The typing environment [x1:A1,..,xn:An] is represented by the
    list [xn:An;..;x1:A1] in reverse order (last added variable comes
    first). Note that it cannot be implemented by a map as the order is
    important. *)
type ctxt = (tvar * term * term option) list

(** Typing context with lifted terms. Used to optimise type checking and avoid
    lifting terms several times. Definitions are not included because these
    contexts are used to create meta variables types, which do not use [let]
    definitions. *)
type bctxt = (tvar * tbox) list

(** Type of unification constraints. *)
type constr = ctxt * term * term

(** Sets and maps of term variables. *)
module Var = struct
  type t = tvar
  let compare = Bindlib.compare_vars
end

module VarSet = Set.Make(Var)
module VarMap = Map.Make(Var)

(** [of_tvar x] injects the [Bindlib] variable [x] in a term. *)
let of_tvar : tvar -> term = fun x -> Vari(x)

(** [new_tvar s] creates a new [tvar] of name [s]. *)
let new_tvar : string -> tvar = Bindlib.new_var of_tvar

(** [new_tvar_ind s i] creates a new [tvar] of name [s ^ string_of_int i]. *)
let new_tvar_ind : string -> int -> tvar = fun s i ->
  new_tvar (Escape.add_prefix s (string_of_int i))

(** [of_tevar x] injects the [Bindlib] variable [x] in a {!type:term_env}. *)
let of_tevar : tevar -> term_env = fun x -> TE_Vari(x)

(** [new_tevar s] creates a new [tevar] with name [s]. *)
let new_tevar : string -> tevar = Bindlib.new_var of_tevar

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

(** Sets and maps of metavariables. *)
module Meta = struct
  type t = meta
  let compare m1 m2 = m2.meta_key - m1.meta_key
end

module MetaSet = Set.Make(Meta)
module MetaMap = Map.Make(Meta)

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

type problem = problem_aux ref

(** Create a new empty problem. *)
let new_problem : unit -> problem = fun () ->
 ref {to_solve  = []; unsolved = []; recompute = false; metas = MetaSet.empty}

(** [create_sym path expo prop opaq name decl typ impl] creates a new symbol
   with path [path], exposition [expo], property [prop], opacity [opaq],
   matching strategy [mstrat], name [name.elt], type [typ], implicit arguments
   [impl], position [name.pos], declaration position [decl.pos], no definition
   and no rules. *)
let create_sym : Path.t -> expo -> prop -> match_strat -> bool ->
  Pos.strloc -> Pos.popt -> term -> bool list -> sym =
  fun sym_path sym_expo sym_prop sym_mstrat sym_opaq
    { elt = sym_name; pos = sym_pos } sym_decl_pos
    typ sym_impl ->
  {sym_path; sym_name; sym_type = ref typ; sym_impl; sym_def = ref None;
   sym_opaq = ref sym_opaq; sym_rules = ref []; sym_dtree = ref Tree_type.empty_dtree;
   sym_mstrat; sym_prop; sym_expo; sym_pos ; sym_decl_pos }

(** [is_constant s] tells whether [s] is a constant. *)
let is_constant : sym -> bool = fun s -> s.sym_prop = Const

(** [is_injective s] tells whether [s] is injective, which is in partiular the
   case if [s] is constant. *)
let is_injective : sym -> bool = fun s ->
  match s.sym_prop with Const | Injec -> true | _ -> !(s.sym_opaq)

(** [is_private s] tells whether the symbol [s] is private. *)
let is_private : sym -> bool = fun s -> s.sym_expo = Privat

(** [is_modulo s] tells whether the symbol [s] is modulo some equations. *)
let is_modulo : sym -> bool = fun s ->
  match s.sym_prop with Assoc _ | Commu | AC _ -> true | _ -> false

(** [unfold t] repeatedly unfolds the definition of the surface constructor of
    [t], until a significant {!type:term} constructor is found.  The term that
    is returned cannot be an instantiated metavariable or term environment nor
    a reference cell ({!constructor:TRef} constructor). Note that the returned
    value is physically equal to [t] if no unfolding was performed. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Meta(m, ts) ->
      begin
        match !(m.meta_value) with
        | None    -> t
        | Some(b) -> unfold (Bindlib.msubst b ts)
      end
  | TRef(r) ->
      begin
        match !r with
        | None    -> t
        | Some(v) -> unfold v
      end
  | _ -> t

(** {b NOTE} that {!val:unfold} must (almost) always be called before matching
    over a value of type {!type:term}. *)

(** [is_abst t] returns [true] iff [t] is of the form [Abst(_)]. *)
let is_abst : term -> bool = fun t ->
  match unfold t with Abst(_) -> true | _ -> false

(** [is_prod t] returns [true] iff [t] is of the form [Prod(_)]. *)
let is_prod : term -> bool = fun t ->
  match unfold t with Prod(_) -> true | _ -> false

(** [is_vari t] returns [true] iff [t] is of the form [Vari(_)]. *)
let is_vari : term -> bool = fun t ->
  match unfold t with Vari(_) -> true | _ -> false

(** [is_patt t] returns [true] iff [t] is of the form [Patt(_)]. *)
let is_patt : term -> bool = fun t ->
  match unfold t with Patt(_) -> true | _ -> false

(** [is_unset m] returns [true] if [m] is not instantiated. *)
let is_unset : meta -> bool = fun m -> !(m.meta_value) = None

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
let is_symb : sym -> term -> bool = fun s t ->
  match unfold t with Symb(r) -> r == s | _ -> false

(** Total order on terms. *)
let cmp : term cmp =
  let rec cmp t t' =
    match unfold t, unfold t' with
    | Vari x, Vari x' -> Bindlib.compare_vars x x'
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
        lex3 Stdlib.compare Stdlib.compare (Array.cmp cmp)
          (i,s,ts) (i',s',ts')
    | TEnv(e,ts), TEnv(e',ts') ->
        lex cmp_tenv (Array.cmp cmp) (e,ts) (e',ts')
    | TRef r, TRef r' -> Stdlib.compare r r'
    | LLet(a,t,u), LLet(a',t',u') ->
        lex3 cmp cmp cmp_binder (a,t,u) (a',t',u')
    | t, t' -> cmp_tag (*cmp_map Stdlib.compare prec*) t t'
  and cmp_binder t t' = let (_,t,t') = Bindlib.unbind2 t t' in cmp t t'
  and cmp_mbinder t t' = let (_,t,t') = Bindlib.unmbind2 t t' in cmp t t'
  and cmp_tenv e e' =
    match e, e' with
    | TE_Vari v, TE_Vari v' -> Bindlib.compare_vars v v'
    | TE_None, TE_None -> 0
    | TE_Some t, TE_Some t' -> cmp_mbinder t t'
    | _ -> cmp_tag (*cmp_map Stdlib.compare prec_tenv*) e e'
  in cmp

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

(** Construction functions of the private type [term]. They ensure some
   invariants:

- In a commutative function symbol application, the first argument is smaller
   than the second one wrt [cmp].

- In an associative and commutative function symbol application, the
   application is built as a left or right comb depending on the associativity
   of the symbol, and arguments are ordered in increasing order wrt [cmp].

- In [LLet(_,_,b)], [Bindlib.binder_constant b = false] (useless let's are
   erased). *)
let mk_Vari x = Vari x
let mk_Type = Type
let mk_Kind = Kind
let mk_Symb x = Symb x
let mk_Prod (a,b) = Prod (a,b)
let mk_Abst (a,b) = Abst (a,b)
let mk_Meta (m,ts) = Meta (m,ts)
let mk_Patt (i,s,ts) = Patt (i,s,ts)
let mk_Wild = Wild
let mk_Plac b = Plac b
let mk_TRef x = TRef x

let mk_LLet (a,t,u) =
  if Bindlib.binder_constant u then Bindlib.subst u Kind else LLet (a,t,u)

let mk_TEnv (te,ts) =
  match te with
  | TE_Some mb -> Bindlib.msubst mb ts
  | _ -> TEnv (te,ts)

(* We make the equality of terms modulo commutative and
   associative-commutative symbols syntactic by always ordering arguments in
   increasing order and by putting them in a comb form.

   The term [t1 + t2 + t3] is represented by the left comb [(t1 + t2) + t3] if
   + is left associative and [t1 + (t2 + t3)] if + is right associative. *)

let mk_bin s t1 t2 = Appl(Appl(Symb s, t1), t2)

(** [mk_left_comb s t ts] builds a left comb of applications of [s] from
   [t::ts] so that [mk_left_comb s t1 [t2; t3] = mk_bin s (mk_bin s t1 t2)
   t3]. *)
let mk_left_comb : sym -> term -> term list -> term = fun s ->
  List.fold_left (mk_bin s)

(** [mk_right_comb s ts t] builds a right comb of applications of [s] to
   [ts@[p]] so that [mk_right_comb s [t1; t2] t3 = mk_bin s t1 (mk_bin s t2
   t3)]. *)
let mk_right_comb : sym -> term list -> term -> term = fun s ->
  List.fold_right (mk_bin s)

(** [left_aliens s t] returns the list of the biggest subterms of [t] not
   headed by [s], assuming that [s] is left associative and [t] is in
   canonical form. This is the reverse of [mk_left_comb]. *)
let left_aliens : sym -> term -> term list = fun s ->
  let rec aliens acc = function
    | [] -> acc
    | u::us ->
        let h, ts = get_args u in
        if is_symb s h then
          match ts with
          | t1 :: t2 :: _ -> aliens (t2 :: acc) (t1 :: us)
          | _ -> aliens (u :: acc) us
        else aliens (u :: acc) us
  in fun t -> aliens [] [t]

(** [right_aliens s t] returns the list of the biggest subterms of [t] not
   headed by [s], assuming that [s] is right associative and [t] is in
   canonical form. This is the reverse of [mk_right_comb]. *)
let right_aliens : sym -> term -> term list = fun s ->
  let rec aliens acc = function
    | [] -> acc
    | u::us ->
        let h, ts = get_args u in
        if is_symb s h then
          match ts with
          | t1 :: t2 :: _ -> aliens (t1 :: acc) (t2 :: us)
          | _ -> aliens (u :: acc) us
        else aliens (u :: acc) us
  in fun t -> let r = aliens [] [t] in
  if Logger.log_enabled () then
    log "right_aliens %a %a = %a"
      Raw.sym s Raw.term t (D.list Raw.term) r;
  r

(* unit test *)
let _ =
  let s =
   create_sym [] Privat (AC true) Eager false (Pos.none "+") None Kind
    [] in
  let t1 = Vari (new_tvar "x1") in
  let t2 = Vari (new_tvar "x2") in
  let t3 = Vari (new_tvar "x3") in
  let left = mk_bin s (mk_bin s t1 t2) t3 in
  let right = mk_bin s t1 (mk_bin s t2 t3) in
  let eq = eq_of_cmp cmp in
  assert (eq (mk_left_comb s t1 [t2; t3]) left);
  assert (eq (mk_right_comb s [t1; t2] t3) right);
  let eq = eq_of_cmp (List.cmp cmp) in
  assert (eq (left_aliens s left) [t1; t2; t3]);
  assert (eq (right_aliens s right) [t3; t2; t1])

(** [mk_Appl t u] puts the application of [t] to [u] in canonical form wrt C
   or AC symbols. *)
let mk_Appl : term * term -> term = fun (t, u) ->
  (* if Logger.log_enabled () then
    log "mk_Appl(%a, %a)" term t term u;
  let r = *)
  match get_args t with
  | Symb s, [t1] ->
      begin
        match s.sym_prop with
        | Commu when cmp t1 u > 0 -> mk_bin s u t1
        | AC true -> (* left associative symbol *)
            let ts = left_aliens s t1 and us = left_aliens s u in
            begin
              match List.sort cmp (ts @ us) with
              | v::vs -> mk_left_comb s v vs
              | _ -> assert false
            end
        | AC false -> (* right associative symbol *)
            let ts = right_aliens s t1 and us = right_aliens s u in
            let vs, v = List.split_last (List.sort cmp (ts @ us))
            in mk_right_comb s vs v
        | _ -> Appl (t, u)
      end
  | _ -> Appl (t, u)
  (* in
  if Logger.log_enabled () then
    log "mk_Appl(%a, %a) = %a" term t term u term r;
  r *)

(** [mk_Appl_not_canonical t u] builds the non-canonical (wrt. C and AC
   symbols) application of [t] to [u]. WARNING: to use only in Sign.link. *)
let mk_Appl_not_canonical : term * term -> term = fun (t, u) -> Appl(t, u)

(** [add_args t args] builds the application of the {!type:term} [t] to a list
    arguments [args]. When [args] is empty, the returned value is (physically)
    equal to [t]. *)
let add_args : term -> term list -> term = fun t ts ->
  List.fold_left (fun t u -> mk_Appl(t,u)) t ts

(** [add_args_map f t ts] is equivalent to [add_args t (List.map f ts)] but
   more efficient. *)
let add_args_map : term -> (term -> term) -> term list -> term = fun t f ts ->
  List.fold_left (fun t u -> mk_Appl(t, f u)) t ts

(** {3 Smart constructors and lifting (related to [Bindlib])} *)

(** [_Vari x] injects the free variable [x] into the {!type:tbox} type so that
    it may be available for binding. *)
let _Vari : tvar -> tbox = Bindlib.box_var

(** [_Type] injects the constructor [Type] into the {!type:tbox} type. *)
let _Type : tbox = Bindlib.box Type

(** [_Kind] injects the constructor [Kind] into the {!type:tbox} type. *)
let _Kind : tbox = Bindlib.box Kind

(** [_Symb s] injects the constructor [Symb(s)] into the {!type:tbox} type. As
    symbols are closed object they do not require lifting. *)
let _Symb : sym -> tbox = fun s -> Bindlib.box (Symb s)

(** [_Appl t u] lifts an application node to the {!type:tbox} type given boxed
   terms [t] and [u]. *)
let _Appl : tbox -> tbox -> tbox =
  Bindlib.box_apply2 (fun t u -> mk_Appl (t,u))

(** [_Appl_not_canonical t u] lifts an application node to the {!type:tbox}
   type given boxed terms [t] and [u], without putting it in canonical form
   wrt. C and AC symbols. WARNING: to use in scoping of rewrite rule LHS only
   as it breaks some invariants. *)
let _Appl_not_canonical : tbox -> tbox -> tbox =
  Bindlib.box_apply2 (fun t u -> Appl (t,u))

(** [_Appl_list a [b1;...;bn]] returns (... ((a b1) b2) ...) bn. *)
let _Appl_list : tbox -> tbox list -> tbox = List.fold_left _Appl

(** [_Appl_Symb f ts] returns the same result that
    _Appl_l ist (_Symb [f]) [ts]. *)
let _Appl_Symb : sym -> tbox list -> tbox = fun f ts ->
  _Appl_list (_Symb f) ts

(** [_Prod a b] lifts a dependent product node to the {!type:tbox} type, given
    a boxed term [a] for the domain of the product, and a boxed binder [b] for
    its codomain. *)
let _Prod : tbox -> tbinder Bindlib.box -> tbox =
  Bindlib.box_apply2 (fun a b -> Prod(a,b))

let _Impl : tbox -> tbox -> tbox =
  let v = new_tvar "_" in fun a b -> _Prod a (Bindlib.bind_var v b)

(** [_Abst a t] lifts an abstraction node to the {!type:tbox}  type,  given  a
    boxed term [a] for the domain type, and a boxed binder [t]. *)
let _Abst : tbox -> tbinder Bindlib.box -> tbox =
  Bindlib.box_apply2 (fun a t -> Abst(a,t))

(** [_Meta m ts] lifts the metavariable [m] to the {!type:tbox} type given its
    environment [ts]. As for symbols in {!val:_Symb}, metavariables are closed
    objects so they do not require lifting. *)
let _Meta : meta -> tbox array -> tbox = fun m ts ->
  Bindlib.box_apply (fun ts -> Meta(m,ts)) (Bindlib.box_array ts)

(** [_Meta_full m ts] is similar to [_Meta m ts] but works with a metavariable
    that is boxed. This is useful in very rare cases,  when metavariables need
    to be able to contain free term environment variables. Using this function
    in bad places is harmful for efficiency but not unsound. *)
let _Meta_full : meta Bindlib.box -> tbox array -> tbox = fun m ts ->
  Bindlib.box_apply2 (fun m ts -> Meta(m,ts)) m (Bindlib.box_array ts)

(** [_Patt i n ts] lifts a pattern variable to the {!type:tbox} type. *)
let _Patt : int option -> string -> tbox array -> tbox = fun i n ts ->
  Bindlib.box_apply (fun ts -> Patt(i,n,ts)) (Bindlib.box_array ts)

(** [_TEnv te ts] lifts a term environment to the {!type:tbox} type. *)
let _TEnv : tebox -> tbox array -> tbox = fun te ts ->
  Bindlib.box_apply2 (fun te ts -> mk_TEnv(te,ts)) te (Bindlib.box_array ts)

(** [_Wild] injects the constructor [Wild] into the {!type:tbox} type. *)
let _Wild : tbox = Bindlib.box Wild

let _Plac : bool -> tbox = fun b ->
  Bindlib.box (mk_Plac b)

(** [_TRef r] injects the constructor [TRef(r)] into the {!type:tbox} type. It
    should be the case that [!r] is [None]. *)
let _TRef : term option ref -> tbox = fun r ->
  Bindlib.box (TRef(r))

(** [_LLet t a u] lifts let binding [let x := t : a in u<x>]. *)
let _LLet : tbox -> tbox -> tbinder Bindlib.box -> tbox =
  Bindlib.box_apply3 (fun a t u -> mk_LLet(a, t, u))

(** [_TE_Vari x] injects a term environment variable [x] into the {!type:tbox}
    type so that it may be available for binding. *)
let _TE_Vari : tevar -> tebox = Bindlib.box_var

(** [_TE_None] injects the constructor [TE_None] into the {!type:tbox} type.*)
let _TE_None : tebox = Bindlib.box TE_None

(** [lift mk_appl t] lifts the {!type:term} [t] to the type {!type:tbox},
   using the function [mk_appl] in the case of an application. This has the
   effect of gathering its free variables, making them available for binding.
   Bound variable names are automatically updated in the process. *)
let lift : (tbox -> tbox -> tbox) -> term -> tbox = fun mk_appl ->
  let rec lift t =
  match unfold t with
  | Vari x      -> _Vari x
  | Type        -> _Type
  | Kind        -> _Kind
  | Symb _      -> Bindlib.box t
  | Prod(a,b)   -> _Prod (lift a) (lift_binder b)
  | Abst(a,t)   -> _Abst (lift a) (lift_binder t)
  | Appl(t,u)   -> mk_appl (lift t) (lift u)
  | Meta(r,m)   -> _Meta r (Array.map lift m)
  | Patt(i,n,m) -> _Patt i n (Array.map lift m)
  | TEnv(te,m)  -> _TEnv (lift_term_env te) (Array.map lift m)
  | Wild        -> _Wild
  | Plac b      -> _Plac b
  | TRef r      -> _TRef r
  | LLet(a,t,u) -> _LLet (lift a) (lift t) (lift_binder u)
  (* We do not use [Bindlib.box_binder] here because it is possible for a free
     variable to disappear from a term through metavariable instantiation. As
     a consequence we must traverse the whole term, even when we find a closed
     binder, so that the metadata on nested binders is also updated. *)
  and lift_binder b =
    let x, t = Bindlib.unbind b in Bindlib.bind_var x (lift t)
  and lift_term_env : term_env -> tebox = function
  | TE_Vari x -> _TE_Vari x
  | TE_None   -> _TE_None
  | TE_Some _ -> assert false (* Unreachable. *)
  in lift

(** [lift t] lifts the {!type:term} [t] to the type {!type:tbox}. This has the
   effect of gathering its free variables, making them available for binding.
   Bound variable names are automatically updated in the process. *)
let lift = lift _Appl
and lift_not_canonical = lift _Appl_not_canonical

(** [bind v lift t] creates a tbinder by binding [v] in [lift t]. *)
let bind : tvar -> (term -> tbox) -> term -> tbinder =
  fun v lift t -> Bindlib.unbox (Bindlib.bind_var v (lift t))
let binds : tvar array -> (term -> tbox) -> term -> tmbinder =
  fun vs lift t -> Bindlib.unbox (Bindlib.bind_mvar vs (lift t))

(** [lift_in c mk_appl t] lifts the {!type:term} [t] in Bindlib context [c] to
   the type {!type:tbox}, using the function [mk_appl] in the case of an
   application. This has the effect of gathering its free variables, making
   them available for binding. Bound variable names are automatically updated
   in the process. *)
let lift_in : (tbox -> tbox -> tbox) -> Bindlib.ctxt -> term -> tbox =
  fun mk_appl ->
  let rec lift c t =
  match unfold t with
  | Vari x      -> _Vari x
  | Type        -> _Type
  | Kind        -> _Kind
  | Symb _      -> Bindlib.box t
  | Prod(a,b)   -> _Prod (lift c a) (lift_binder c b)
  | Abst(a,t)   -> _Abst (lift c a) (lift_binder c t)
  | Appl(t,u)   -> mk_appl (lift c t) (lift c u)
  | Meta(r,m)   -> _Meta r (Array.map (lift c) m)
  | Patt(i,n,m) -> _Patt i n (Array.map (lift c) m)
  | TEnv(te,m)  -> _TEnv (lift_term_env te) (Array.map (lift c) m)
  | Wild        -> _Wild
  | Plac b      -> _Plac b
  | TRef r      -> _TRef r
  | LLet(a,t,u) -> _LLet (lift c a) (lift c t) (lift_binder c u)
  (* We do not use [Bindlib.box_binder] here because it is possible for a free
     variable to disappear from a term through metavariable instantiation. As
     a consequence we must traverse the whole term, even when we find a closed
     binder, so that the metadata on nested binders is also updated. *)
  and lift_binder c b =
    let x, t, c = Bindlib.unbind_in c b in Bindlib.bind_var x (lift c t)
  and lift_term_env : term_env -> tebox = function
  | TE_Vari x -> _TE_Vari x
  | TE_None   -> _TE_None
  | TE_Some _ -> assert false (* Unreachable. *)
  in lift

(** [cleanup t] builds a copy of the {!type:term} [t] where every instantiated
   metavariable, instantiated term environment, and reference cell has been
   eliminated using {!val:unfold}. Another effect of the function is that the
   the names of bound variables are updated. This is useful to avoid any form
   of "visual capture" while printing terms. *)
let cleanup : ?ctxt:Bindlib.ctxt -> term -> term =
  fun ?(ctxt=Bindlib.empty_ctxt) t ->
  Bindlib.unbox (lift_in _Appl_not_canonical ctxt t)

(** Positions in terms in reverse order. The i-th argument of a constructor
   has position i-1. *)
type subterm_pos = int list

let subterm_pos : subterm_pos pp = fun ppf l -> D.(list int) ppf (List.rev l)

(** Type of critical pair positions (pos,l,r,p,l_p). *)
type cp_pos = Pos.popt * term * term * subterm_pos * term

(** [term_of_rhs r] converts the RHS (right hand side) of the rewriting rule
    [r] into a term. The bound higher-order variables of the original RHS are
    substituted using [Patt] constructors. They are thus represented as their
    LHS counterparts. This is a more convenient way of representing terms when
    analysing confluence or termination. *)
let term_of_rhs : rule -> term = fun r ->
  let f i x =
    let vars = Array.init r.arities.(i) (new_tvar_ind "x") in
    let p = _Patt (Some i) (Bindlib.name_of x) (Array.map _Vari vars) in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar vars p))
  in
  Bindlib.msubst r.rhs (Array.mapi f r.vars)

(** Type of a symbol and a rule. *)
type sym_rule = sym * rule

let lhs : sym_rule -> term = fun (s, r) -> add_args (mk_Symb s) r.lhs
let rhs : sym_rule -> term = fun (_, r) -> term_of_rhs r
