(** Internal representation of terms.

   This module contains the definition of the internal representation of
   terms, together with smart constructors and low level operation. The
   representation strongly relies on the {!module:Bindlib} library, which
   provides a convenient abstraction to work with binders.

    @see <https://rlepigre.github.io/ocaml-bindlib/> *)

open Timed
open Lplib.Base
open Common

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
type term = private
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
  (** [Plac b] is a placeholder, or hole, for not given terms. Boolean
      [b] is true if the placeholder stands for a type. *)
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
    be enforced for "mode" consistency (see {!type:prop}).  *)
and sym =
  { sym_expo  : expo (** Visibility. *)
  ; sym_path  : Path.t (** Module in which the symbol is defined. *)
  ; sym_name  : string (** Name. *)
  ; sym_type  : term ref (** Type. *)
  ; sym_impl  : bool list (** Implicit arguments ([true] meaning implicit). *)
  ; sym_prop  : prop (** Property. *)
  ; sym_def   : term option ref (** Definition with ≔. *)
  ; sym_opaq  : bool (** Opacity. *)
  ; sym_rules : rule list ref (** Rewriting rules. *)
  ; sym_mstrat: match_strat (** Matching strategy. *)
  ; sym_dtree : dtree ref (** Decision tree used for matching. *)
  ; sym_pos   : Pos.popt (** Position in source file. *) }

(** {b NOTE} that {!field:sym_type} holds a (timed) reference for a  technical
    reason related to the writing of signatures as binary files  (in  relation
    to {!val:Sign.link} and {!val:Sign.unlink}).  This is necessary to enforce
    ensure that two identical symbols are always physically equal, even across
    signatures. It should NOT be otherwise mutated. *)

(** {b NOTE} we maintain the invariant that {!field:sym_impl} never ends  with
    [false]. Indeed, this information would be redundant. If a symbol has more
    arguments than there are booleans in the list then the extra arguments are
    all explicit. Finally, note that {!field:sym_impl} is empty if and only if
    the symbol has no implicit parameters. *)

(** {b NOTE} the value of the {!field:sym_prop} field of symbols restricts the
    value of their {!field:sym_def} and {!field:sym_rules} fields. A symbol is
    not allowed to be given rewriting rules (or a definition) when its mode is
    set to {!constructor:Const}. Moreover, a symbol should not be given at
    the same time a definition (i.e., {!field:sym_def} different from [None])
    and rewriting rules (i.e., {!field:sym_rules} is non-empty). *)

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

(** The LHS (or pattern) of a rewriting rule is always formed of a head symbol
    (on which the rule is defined) applied to a list of pattern arguments. The
    list of arguments is given in {!field:lhs},  but the head symbol itself is
    not stored in the rule, since rules are stored in symbols.  In the pattern
    arguments of a LHS, [Patt(i,s,env)] is used to represent pattern variables
    that are identified by a name [s] (unique in a rewriting rule). They carry
    an environment [env] that should only contain distinct variables (terms of
    the form [Vari(x)]).  They correspond to the set of all the variables that
    may appear free in a matched term. The optional integer [i] corresponds to
    the reserved index for the matched term in the environment of the RHS
    during matching.

    For instance, with the rule [f $X $Y $Y $Z ↪ $X]:
     - [$X] is represented by [Patt(Some 0, "X", [||])] since it occurs in the
       RHS of the rule (and it is actually the only one),
     - [$Y] is represented by [Patt(Some 1, "Y", [||])] as it occurs more than
       once in the LHS (the rule is non-linear in this variable),
     - [$Z] is represented by [Patt(Some 2, "Z", [||])] even though it is not
       bound in the RHS and it appears linearly. Note that wildcards (in the
       concrete syntax) are represented in the same way, and with a unique
       name (in the rule) that is generated automatically.

    Then, the term [f t u v w] matches the LHS with a substitution represented
    by an array of terms (or rather “term environments”) [a] of length 3 if we
    have [a.(0) = t], [a.(1) = u], [a.(1) = v] and [a.(2) = w].

    {b TODO} memorising [w] in the substitution is sub-optimal. In practice,
    the term matched by [$Z] should be ignored. *)

(** {b NOTE} that the second parameter of the {!constructor:Patt}  constructor
    holds an array of terms. This is essential for variables binding: using an
    array of variables would NOT suffice. *)

(** {b NOTE} that the value of the {!field:arity} field  (of a rewriting rule)
    gives the number of arguments contained in its LHS. As a consequence,  the
    value of [r.arity] is always equal to [List.length r.lhs] and it gives the
    minimal number of arguments required to match the LHS of the rule. *)

(** The RHS (or action) or a rewriting rule is represented by a term, in which
    (higher-order) variables representing "terms with environments" (see the
    {!type:term_env} type) are bound. To effectively apply the rewriting rule,
    these  bound variables must be substituted using "terms with environments"
    that are constructed when matching the LHS of the rule. *)

(** All variables of rewriting rules that appear in the RHS must appear in the
   LHS. This constraint is checked in {!module:Tool.Sr}.In the case of
   unification rules, we allow variables to appear only in the RHS.  In that
   case, these variables are replaced by fresh meta-variables each time the
   rule is used.  The last {!field:Term.rule.xvars_nb} variables of
   {!field:Term.rule.vars} are such RHS-only variables. *)

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
  | TE_None (** Dummy term environment (used during matching). *)

(** The {!constructor:TEnv}[(te,env)] constructor intuitively corresponds to a
    term [te] with free variables together with an explicit environment [env].
    Note that the binding of the environment actually occurs in [te], when the
    constructor is of the form {!constructor:TE_Some}[(b)]. Indeed, [te] holds
    a multiple binder [b] that binds every free variables of the term at once.
    We then apply the substitution by performing a Bindlib substitution of [b]
    with the environment [env]. *)

(** During evaluation, we only try to apply rewriting rules when we reduce the
   application of a symbol [s] to a list of argument [ts]. At this point, the
   symbol [s] contains every rule [r] that can potentially be applied in its
   {!field:sym_rules} field. To check if a rule [r] applies, we match the
   elements of [r.lhs] with those of [ts] while building an environment [env]
   of type [{!type:Term.term_env} array]. During this process, a pattern of
   the form {!constructor:Patt}[(Some i,s,e)] matched against a term [u] will
   results in [env.(i)] being set to [u]. If all terms of [ts] can be matched
   against corresponding patterns, then environment [env] is fully constructed
   and it can hence be substituted in [r.rhs] with [Bindlib.msubst r.rhs env]
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
  ; meta_type  : term ref (** Type. *)
  ; meta_arity : int (** Arity (environment size). *)
  ; meta_value : tmbinder option ref (** Definition. *) }

and tbinder = (term, term) Bindlib.binder

and tmbinder = (term, term) Bindlib.mbinder

and tvar = term Bindlib.var

and tevar = term_env Bindlib.var

type tbox = term Bindlib.box

type tebox = term_env Bindlib.box

(** Minimize [impl] to enforce our invariant (see {!type:Term.sym}). *)
val minimize_impl : bool list -> bool list

(** Basic printing function (for debug). *)
val pp_term : term pp

(** Typing context associating a [Bindlib] variable to a type and possibly a
    definition. The typing environment [x1:A1,..,xn:An] is represented by the
    list [xn:An;..;x1:A1] in reverse order (last added variable comes
    first). *)
type ctxt = (tvar * term * term option) list

(** Typing context with lifted terms. Used to optimise type checking and avoid
    lifting terms several times. Definitions are not included because these
    contexts are used to create meta variables types, which do not use [let]
    definitions. *)
type bctxt = (tvar * tbox) list

(** Type of unification constraints. *)
type constr = ctxt * term * term

(** Sets and maps of term variables. *)
module Var : Map.OrderedType with type t = tvar

module VarSet : Set.S with type elt = tvar
module VarMap : Map.S with type key = tvar

(** [of_tvar x] injects the [Bindlib] variable [x] in a term. *)
val of_tvar : tvar -> term

(** [new_tvar s] creates a new [tvar] of name [s]. *)
val new_tvar : string -> tvar

(** [new_tvar_ind s i] creates a new [tvar] of name [s ^ string_of_int i]. *)
val new_tvar_ind : string -> int -> tvar

(** [of_tevar x] injects the [Bindlib] variable [x] in a {!type:term_env}. *)
val of_tevar : tevar -> term_env

(** [new_tevar s] creates a new [tevar] with name [s]. *)
val new_tevar : string -> tevar

(** Sets and maps of symbols. *)
module Sym : Map.OrderedType with type t = sym
module SymSet : Set.S with type elt = sym
module SymMap : Map.S with type key = sym

(** [create_sym path expo prop opaq name typ impl] creates a new symbol with
   position [pos], path [path], exposition [expo], property [prop], opacity
   [opaq], matching strategy [mstrat], name [name.elt], type [typ], implicit
   arguments [impl], position [name.pos], no definition and no rules. *)
val create_sym : Path.t -> expo -> prop -> match_strat -> bool ->
  Pos.strloc -> term -> bool list -> sym

(** [is_constant s] tells whether the symbol is a constant. *)
val is_constant : sym -> bool

(** [is_injective s] tells whether [s] is injective, which is in partiular the
   case if [s] is constant. *)
val is_injective : sym -> bool

(** [is_private s] tells whether the symbol [s] is private. *)
val is_private : sym -> bool

(** [is_modulo s] tells whether the symbol [s] is modulo some equations. *)
val is_modulo : sym -> bool

(** Sets and maps of metavariables. *)
module Meta : Map.OrderedType with type t = meta
module MetaSet : Set.S with type elt = Meta.t
module MetaMap : Map.S with type key = Meta.t

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
val new_problem : unit -> problem

(** [unfold t] repeatedly unfolds the definition of the surface constructor of
   [t], until a significant {!type:term} constructor is found. The term that
   is returned cannot be an instantiated metavariable, term environment or
   reference cell. The returned value is physically equal to [t] if no
   unfolding was performed. *)
val unfold : term -> term

(** {b NOTE} that {!val:unfold} must (almost) always be called before matching
    over a value of type {!type:term}. *)

(** Total orders terms. *)
val cmp : term cmp

(** [is_abst t] returns [true] iff [t] is of the form [Abst(_)]. *)
val is_abst : term -> bool

(** [is_prod t] returns [true] iff [t] is of the form [Prod(_)]. *)
val is_prod : term -> bool

(** [is_unset m] returns [true] if [m] is not instantiated. *)
val is_unset : meta -> bool

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
val is_symb : sym -> term -> bool

(** [get_args t] decomposes the {!type:term} [t] into a pair [(h,args)], where
    [h] is the head term of [t] and [args] is the list of arguments applied to
    [h] in [t]. The returned [h] cannot be an [Appl] node. *)
val get_args : term -> term * term list

(** [get_args_len t] is similar to [get_args t] but it also returns the length
    of the list of arguments. *)
val get_args_len : term -> term * term list * int

(** Construction functions of the private type [term]. They ensure some
   invariants:

- In a commutative function symbol application, the first argument is smaller
   than the second one wrt [cmp].

- In an associative and commutative function symbol application, the
   application is built as a left or right comb depending on the associativity
   of the symbol, and arguments are ordered in increasing order wrt [cmp].

- In [LLet(_,_,b)], [Bindlib.binder_constant b = false] (useless let's are
   erased). *)
val mk_Vari : tvar -> term
val mk_Type : term
val mk_Kind : term
val mk_Symb : sym -> term
val mk_Prod : term * tbinder -> term
val mk_Abst : term * tbinder -> term
val mk_Appl : term * term -> term
val mk_Meta : meta * term array -> term
val mk_Patt : int option * string * term array -> term
val mk_TEnv : term_env * term array -> term
val mk_Wild : term
val mk_Plac : bool -> term
val mk_TRef : term option ref -> term
val mk_LLet : term * term * tbinder -> term

(** [mk_Appl_not_canonical t u] builds the non-canonical (wrt. C and AC
   symbols) application of [t] to [u]. WARNING: to use only in Sign.link. *)
val mk_Appl_not_canonical : term * term -> term

(** [add_args t args] builds the application of the {!type:term} [t] to a list
    arguments [args]. When [args] is empty, the returned value is (physically)
    equal to [t]. *)
val add_args : term -> term list -> term

(** [add_args_map f t ts] is equivalent to [add_args t (List.map f ts)] but
   more efficient. *)
val add_args_map : term -> (term -> term) -> term list -> term

(** {3 Smart constructors and lifting (related to [Bindlib])} *)

(** [_Vari x] injects the free variable [x] into the {!type:tbox} type so that
    it may be available for binding. *)
val _Vari : tvar -> tbox

(** [_Type] injects the constructor [Type] into the {!type:tbox} type. *)
val _Type : tbox

(** [_Kind] injects the constructor [Kind] into the {!type:tbox} type. *)
val _Kind : tbox

(** [_Symb s] injects the constructor [Symb(s)] into the {!type:tbox} type. As
    symbols are closed object they do not require lifting. *)
val _Symb : sym -> tbox

(** [_Appl t u] lifts an application node to the {!type:tbox} type given boxed
   terms [t] and [u]. *)
val _Appl : tbox -> tbox -> tbox

(** [_Appl_not_canonical t u] lifts an application node to the {!type:tbox}
   type given boxed terms [t] and [u], without putting it in canonical form
   wrt. C and AC symbols. WARNING: to use in scoping of rewrite rule LHS only
   as it breaks some invariants. *)
val _Appl_not_canonical : tbox -> tbox -> tbox

(** [_Appl_list a [b1;...;bn]] returns (... ((a b1) b2) ...) bn. *)
val _Appl_list : tbox -> tbox list -> tbox

(** [_Appl_Symb f ts] returns the same result that
    _Appl_l ist (_Symb [f]) [ts]. *)
val _Appl_Symb : sym -> tbox list -> tbox

(** [_Prod a b] lifts a dependent product node to the {!type:tbox} type, given
    a boxed term [a] for the domain of the product, and a boxed binder [b] for
    its codomain. *)
val _Prod : tbox -> tbinder Bindlib.box -> tbox

val _Impl : tbox -> tbox -> tbox

(** [_Abst a t] lifts an abstraction node to the {!type:tbox}  type,  given  a
    boxed term [a] for the domain type, and a boxed binder [t]. *)
val _Abst : tbox -> tbinder Bindlib.box -> tbox

(** [_Meta m ar] lifts the metavariable [m] to the {!type:tbox} type given its
    environment [ar]. As for symbols in {!val:_Symb}, metavariables are closed
    objects so they do not require lifting. *)
val _Meta : meta -> tbox array -> tbox

(** [_Meta_full m ar] is similar to [_Meta m ar] but works with a metavariable
    that is boxed. This is useful in very rare cases,  when metavariables need
    to be able to contain free term environment variables. Using this function
    in bad places is harmful for efficiency but not unsound. *)
val _Meta_full : meta Bindlib.box -> tbox array -> tbox

(** [_Patt i n ar] lifts a pattern variable to the {!type:tbox} type. *)
val _Patt : int option -> string -> tbox array -> tbox

(** [_TEnv te ar] lifts a term environment to the {!type:tbox} type. *)
val _TEnv : tebox -> tbox array -> tbox

(** [_Wild] injects the constructor [Wild] into the {!type:tbox} type. *)
val _Wild : tbox

(** [_Plac] injects the constructor [Plac] into the {!type:tbox} type. *)
val _Plac : bool -> tbox

(** [_TRef r] injects the constructor [TRef(r)] into the {!type:tbox} type. It
    should be the case that [!r] is [None]. *)
val _TRef : term option ref -> tbox

(** [_LVal t a u] lifts val binding [val x := t : a in u<x>]. *)
val _LLet : tbox -> tbox -> tbinder Bindlib.box -> tbox

(** [_TE_Vari x] injects a term environment variable [x] into the {!type:tbox}
    type so that it may be available for binding. *)
val _TE_Vari : tevar -> tebox

(** [_TE_None] injects the constructor [TE_None] into the {!type:tbox} type.*)
val _TE_None : tebox

(** [lift t] lifts the {!type:term} [t] to the {!type:tbox} type. This has the
    effect of gathering its free variables, making them available for binding.
    Bound variable names are automatically updated in the process. *)
val lift : term -> tbox

(** [cleanup t] builds a copy of the {!type:term} [t] where every instantiated
   metavariable, instantiated term environment, and reference cell has been
   eliminated using {!val:unfold}. Another effect of the function is that the
   the names of bound variables are updated. This is useful to avoid any form
   of "visual capture" while printing terms. *)
val cleanup : term -> term
