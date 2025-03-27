(** Internal representation of terms.

   This module contains the definition of the internal representation of
   terms, together with smart constructors and low level operation. *)

open Lplib open Base
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

(** Reduction strategy. *)
type red_strat =
  | Innermost
  (** Arguments are normalized before trying to apply a rewrite rule. Strategy
      used for symbols with rules matching on AC symbols. *)
  | Outermost
  (** Arguments are reduced when trying to apply a rewrite rule. This is the
      default. *)

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

(** Type for free variables. *)
type var

(** Type for binders. *)
type binder
type mbinder

(** Type of bound variables. *)
type bvar

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
    are considered invalid in unrelated code. *)
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
  (** [Plac b] is a placeholder, or hole, for not given terms. Boolean
      [b] is true if the placeholder stands for a type. *)
  | TRef of term option Timed.ref
  (** Reference cell (used in surface matching). *)
  | LLet of term * term * binder
  (** [LLet(a, t, u)] is [let x : a ≔ t in u] (with [x] bound in [u]). *)

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
  ; sym_rstrat: red_strat Timed.ref (** Reduction strategy. *)
  ; sym_dtree : dtree Timed.ref (** Decision tree used for matching. *)
  ; sym_pos   : Pos.popt (** Position in source file of symbol name. *)
  ; sym_decl_pos : Pos.popt (** Position in source file of symbol declaration
                                without its definition. *) }

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
  ; rhs      : term (** Right hand side (RHS). *)
  ; arity    : int (** Required number of arguments to be applicable. *)
  ; arities  : int array
  (** Arities of the pattern variables bound in the RHS. *)
  ; vars_nb  : int (** Number of variables in [lhs]. *)
  ; xvars_nb : int (** Number of variables in [rhs] but not in [lhs]. *)
  ; rule_pos : Pos.popt (** Position of the rule in the source file. *) }

(** The LHS (or pattern) of a rewriting rule is always formed of a head symbol
    (on which the rule is defined) applied to a list of pattern arguments. The
    list of arguments is given in {!field:lhs},  but the head symbol itself is
    not stored in the rule, since rules are stored in symbols.  In the pattern
    arguments of a LHS, [Patt(i,s,ts)] is used to represent pattern variables
    that are identified by a name [s] (unique in a rewriting rule). They carry
    an environment [ts] that should only contain distinct variables (terms of
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
    by an array of terms [a] of length 3 if we
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

(** All variables of rewriting rules that appear in the RHS must appear in the
   LHS. This constraint is checked in {!module:Tool.Sr}.In the case of
   unification rules, we allow variables to appear only in the RHS.  In that
   case, these variables are replaced by fresh meta-variables each time the
   rule is used.  The last {!field:Term.rule.xvars_nb} variables of
   {!field:Term.rule.vars} are such RHS-only variables. *)

(** During evaluation, we only try to apply rewriting rules when we reduce the
   application of a symbol [s] to a list of argument [ts]. At this point, the
   symbol [s] contains every rule [r] that can potentially be applied in its
   {!field:sym_rules} field. To check if a rule [r] applies, we match the
   elements of [r.lhs] with those of [ts] while building an environment [env].
   During this process, a pattern of
   the form {!constructor:Patt}[(Some i,_,_)] matched against a term [u] will
   results in [env.(i)] being set to [u]. If all terms of [ts] can be matched
   against corresponding patterns, then environment [env] is fully constructed
   and it can hence be substituted in [r.rhs] with [msubst r.rhs env]
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

(** [binder_name b] gives the name of the bound variable of [b]. *)
val binder_name : binder -> string

(** [mbinder_names b] gives the names of the bound variables of [b]. *)
val mbinder_names : mbinder -> string array

(** [mbinder_arity b] gives the arity of the [mbinder]. *)
val mbinder_arity : mbinder -> int

(** Minimize [impl] to enforce our invariant (see {!type:Term.sym}). *)
val minimize_impl : bool list -> bool list

(** [create_sym path expo prop mstrat opaq name pos typ impl] creates a new
    symbol with path [path], exposition [expo], property [prop], opacity
    [opaq], matching strategy [mstrat], name [name.elt], type [typ], implicit
    arguments [impl], position [name.pos], declaration position [pos], no
    definition and no rules. *)
val create_sym : Path.t -> expo -> prop -> match_strat -> bool ->
  Pos.strloc -> Pos.popt -> term -> bool list -> sym

(** [is_constant s] tells whether the symbol is a constant. *)
val is_constant : sym -> bool

(** [is_injective s] tells whether [s] is injective, which is in partiular the
   case if [s] is constant. *)
val is_injective : sym -> bool

(** [is_private s] tells whether the symbol [s] is private. *)
val is_private : sym -> bool

(** [is_modulo s] tells whether the symbol [s] is modulo some equations. *)
val is_modulo : sym -> bool
val is_ac : sym -> bool

(** Sets and maps of symbols. *)
module Sym : Map.OrderedType with type t = sym
module SymSet : Set.S with type elt = sym
module SymMap : Map.S with type key = sym

(** [compare_vars x y] safely compares [x] and [y].  Note that it is unsafe to
    compare variables using [Pervasive.compare]. *)
val compare_vars : var -> var -> int

(** [eq_vars x y] safely computes the equality of [x] and [y]. Note that it is
    unsafe to compare variables with the polymorphic equality function. *)
val eq_vars : var -> var -> bool

(** [new_var s] creates a new [var] of name [s]. *)
val new_var : string -> var

(** [new_var_ind s i] creates a new [var] of name [s ^ string_of_int i]. *)
val new_var_ind : string -> int -> var

(** [base_name x] returns the base name of the variable [x]. Note that this
    base name is not unique: two distinct variables may have the same name. *)
val base_name : var -> string

(** [uniq_name x] returns a string uniquely identifying the variable [x]. *)
val uniq_name : var -> string

(** Sets and maps of term variables. *)
module Var : Map.OrderedType with type t = var
module VarSet : Set.S with type elt = var
module VarMap : Map.S with type key = var

(** [is_unset m] returns [true] if [m] is not instantiated. *)
val is_unset : meta -> bool

(** Sets and maps of metavariables. *)
module Meta : Map.OrderedType with type t = meta
module MetaSet : Set.S with type elt = Meta.t
module MetaMap : Map.S with type key = Meta.t

(** [unfold t] repeatedly unfolds the definition of the surface constructor of
   [t], until a significant {!type:term} constructor is found. The term that
   is returned cannot be an instantiated metavariable, term environment or
   reference cell. The returned value is physically equal to [t] if no
   unfolding was performed. *)
val unfold : term -> term

(** {b NOTE} that {!val:unfold} must (almost) always be called before matching
    over a value of type {!type:term}. *)

(** [is_abst t] returns [true] iff [t] is of the form [Abst(_)]. *)
val is_abst : term -> bool

(** [is_prod t] returns [true] iff [t] is of the form [Prod(_)]. *)
val is_prod : term -> bool

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
val is_symb : sym -> term -> bool

(** [get_args t] decomposes the {!type:term} [t] into a pair [(h,args)], where
    [h] is the head term of [t] and [args] is the list of arguments applied to
    [h] in [t]. The returned [h] cannot be an [Appl] node. *)
val get_args : term -> term * term list

(** [get_args_len t] is similar to [get_args t] but it also returns the length
    of the list of arguments. *)
val get_args_len : term -> term * term list * int

(** Total orders terms. *)
val cmp : term cmp

(** Build a non-dependent product. *)
val mk_Arro : term * term -> term

(** Curryfied versions of some constructors. *)
val mk_Vari : var -> term
val mk_Abst : term * binder -> term
val mk_Prod : term * binder -> term

(** [add_args t args] builds the application of the {!type:term} [t] to a list
    arguments [args]. When [args] is empty, the returned value is (physically)
    equal to [t]. *)
val add_args : term -> term list -> term

(** [add_args_map f t xs] is equivalent to [add_args t (List.map f xs)] but
   more efficient. *)
val add_args_map : term -> ('a -> term) -> 'a list -> term

(** [subst b v] substitutes the variable bound by [b] with the value [v]. *)
val subst : binder -> term -> term

(** [msubst b vs] substitutes the variables bound by [b] with the values [vs].
   Note that the length of the [vs] array should match the arity of the
   multiple binder [b]. *)
val msubst : mbinder -> term array -> term

(** [unbind b] substitutes the binder [b] by a fresh variable of name [name]
   if given, or the binder name otherwise. The variable and the result of the
   substitution are returned. *)
val unbind : ?name:string -> binder -> var * term

(** [unbind2 f g] is similar to [unbind f], but it substitutes two binders [f]
   and [g] at once using the same fresh variable. *)
val unbind2 : ?name:string -> binder -> binder -> var * term * term

(** [unmbind b] substitutes the multiple binder [b] with fresh variables. This
    function is analogous to [unbind] for binders. Note that the names used to
    create the fresh variables are based on those of the multiple binder. *)
val unmbind : mbinder -> var array * term

(** [bind_var x b] binds the variable [x] in [b], producing a binder. *)
val bind_var  : var -> term -> binder

(** [binder f b] applies f inside [b]. *)
val binder : (term -> term) -> binder -> binder

(** [bind_mvar xs b] binds the variables of [xs] in [b] to get a binder.
    It is the equivalent of [bind_var] for multiple variables. *)
val bind_mvar : var array -> term -> mbinder

(** [binder_occur b] tests whether the bound variable occurs in [b]. *)
val binder_occur : binder -> bool
val mbinder_occur : mbinder -> int -> bool

(** [is_closed b] checks whether the [term] [b] is closed. *)
val is_closed : term -> bool
val is_closed_mbinder : mbinder -> bool

(** [occur x b] tells whether variable [x] occurs in [b]. *)
val occur : var -> term -> bool
val occur_mbinder : var -> mbinder -> bool

(** Patt substitution. *)
val subst_patt : mbinder option array -> term -> term

(** [cleanup t] unfold all metas and TRef's in [t]. *)
val cleanup : term -> term

(** Typing context associating a variable to a type and possibly a
    definition. The typing environment [x1:A1,..,xn:An] is represented by the
    list [xn:An;..;x1:A1] in reverse order (last added variable comes
    first). *)
type ctxt = (var * term * term option) list

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
val new_problem : unit -> problem

(** Positions in terms in reverse order. The i-th argument of a constructor
   has position i-1. *)
type subterm_pos = int list

val subterm_pos : subterm_pos pp

(** Type of critical pair positions (pos,l,r,p,l_p). *)
type cp_pos = Pos.popt * term * term * subterm_pos * term

(** Type of a symbol and a rule. *)
type sym_rule = sym * rule

val lhs : sym_rule -> term
val rhs : sym_rule -> term

(** Basic printing function (for debug). *)
module Raw : sig
  val term : term pp
  val ctxt : ctxt pp
end
