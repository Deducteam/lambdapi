(** Term representation.

    This module contains the definition of the core abstract syntax tree (AST)
    of the language, together with smart constructors and low level operation.
    The representation strongly relies on the {!module:Bindlib} library, which
    provides a convenient abstraction to work with binders.

    @see <https://rlepigre.github.io/ocaml-bindlib/> *)

open Extra
open Timed

(** {3 Term (and symbol) representation} *)

(** Representation of a term (or types) in a general sense. Values of the type
    are also used, for example, in the representation of patterns or rewriting
    rules. Specific constructors are included for such applications,  and they
    are considered invalid in unrelated code. *)
type term =
  | Vari of term Bindlib.var
  (** Free variable. *)
  | Type
  (** "TYPE" constant. *)
  | Kind
  (** "KIND" constant. *)
  | Symb of sym * pp_hint
  (** User-defined symbol. *)
  | Prod of term * (term, term) Bindlib.binder
  (** Dependent product. *)
  | Abst of term * (term, term) Bindlib.binder
  (** Abstraction (with domain type). *)
  | Appl of term * term
  (** Term application. *)
  | Meta of meta * term array
  (** Metavariable application (used by unification and for proof goals). *)
  | Patt of int option * string * term array
  (** Pattern variable application (only used in a rewriting rules LHS). *)
  | TEnv of term_env * term array
  (** Term environment (only used in a rewriting rules RHS). *)
  | Wild
  (** Wildcard (only used for surface matching, never in a LHS). *)
  | TRef of term option ref
  (** Reference cell (only used for surface matching). *)

(** {b NOTE} that a wildcard "_" of the concrete (source code) syntax may have
    a different representation depending on the application. For instance, the
    {!constructor:Wild} constructor is only used when matching patterns (e.g.,
    with the "rewrite" tactic). In the LHS of a rewriting {!type:rule}, we use
    the {!constructor:Patt} constructor to represend wildcards of the concrete
    syntax. They are thus considered to be fresh, unused pattern variables. *)

(** Representation of a user-defined symbol. Symbols carry a "mode" indicating
    whether they may be given rewriting rules or a definition. Invariants must
    be enforced for "mode" consistency (see {!type:sym_mode}).  *)
 and sym =
  { sym_name  : string
  (** Name of the symbol. *)
  ; sym_type  : term ref
  (** Type of the symbol. *)
  ; sym_path  : Files.module_path
  (** Module in which it is defined. *)
  ; sym_def   : term option ref
  (** Definition of the symbol. *)
  ; sym_impl  : bool list
  (** Implicitness of the first arguments ([true] meaning implicit). *)
  ; sym_rules : rule list ref
  (** Rewriting rules for the symbol. *)
  ; sym_tree : tree ref
  (** Tree for rule selection. *)
  ; sym_mode  : sym_mode
  (** Tells what kind of symbol it is. *) }

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

(** Possible modes for a symbol. It is given at the declaration of the symbol,
    and it cannot be changed subsequently. *)
 and sym_mode =
  | Const
  (** The symbol is constant: it has no definition and no rewriting rule. *)
  | Defin
  (** The symbol may have a definition or rewriting rules (but NOT both). *)
  | Injec
  (** Same as [Defin], but the symbol is considered to be injective. *)

(** {b NOTE} the value of the {!field:sym_mode} field of symbols restricts the
    value of their {!field:sym_def} and {!field:sym_rules} fields. A symbol is
    not allowed to be given rewriting rules (or a definition) when its mode is
    set to {!constructor:Const}. Moreover, a symbol should not be given at the
    same time a definition (i.e., {!field:sym_def} different from [None])  and
    rewriting rules (i.e., {!field:sym_rules} is non-empty). *)

(** Pretty-printing hint for a symbol. One hint is attached to each occurrence
    of a symbol, depending on the corresponding concrete (source code) syntax.
    The aim of hints is to preserve as much as possible the syntax used by the
    user in the concrete (source file) syntax. *)
 and pp_hint =
  | Nothing
  (** Just print the name of the symbol. *)
  | Qualified
  (** Fully qualify the symbol name. *)
  | Alias  of string
  (** Use the given alias as qualifier. *)
  | Binary of string
  (** Show as the given binary operator. *)

(** {3 Representation of rewriting rules} *)

(** Representation of a rewriting rule. A rewriting rule is mainly formed of a
    LHS (left hand side),  which is the pattern that should be matched for the
    rule to apply, and a RHS (right hand side) giving the action to perform if
    the rule applies. More explanations are given below. *)
 and rule =
  { lhs   : term list
  (** Left hand side (or LHS). *)
  ; rhs   : (term_env, term) Bindlib.mbinder
  (** Right hand side (or RHS). *)
  ; arity : int
  (** Required number of arguments to be applicable. *)
  ; vars  : (string * int) array
  (** Name and arity of the pattern variables bound in the RHS. *) }

(** The LHS (or pattern) of a rewriting rule is always formed of a head symbol
    (on which the rule is defined) applied to a list of pattern arguments. The
    list of arguments is given in {!field:lhs},  but the head symbol itself is
    not stored in the rule, since rules are stored in symbols.  In the pattern
    arguments of a LHS, [Patt(i,s,env)] is used to represent pattern variables
    that are identified by a name [s] (unique in a rewriting rule). They carry
    an environment [env] that should only contain distinct variables (terms of
    the form [Vari(x)]).  They correspond to the set of all the variables that
    may appear free in a matched term. The optional integer [i] corresponds to
    the reserved index (if any) for the matched term in the environment of the
    RHS during matching. When [i] is [None], then the variable is not bound in
    the RHS. If it is [Some(_)], then the variables is bound in the RHS, or it
    appears non-linearly in the LHS.

    For instance, with the rule [f &X &Y &Y &Z → &X]:
     - [&X] is represented by [Patt(Some 0, "X", [||])] since it occurs in the
       RHS of the rule (and it is actually the only one),
     - [&Y] is represented by [Patt(Some 1, "Y", [||])] at it occurs more than
       once in the LHS (the rule is non-linear in this variable),
     - [&Z] is represented by [Patt(None, "Z", [||])] since it is only appears
       once in the LHS, and it is not used in the RHS. Note that wildcards (in
       the concrete syntax) are represented in the same way, and with a unique
       name (in the rule) that is generated automatically.

    Then, the term [f t u v w] matches the LHS with a substitution represented
    by an array of terms (or rather “term environments”) [a] of length 2 if we
    have [a.(0) = t], [a.(1) = u] and [a.(1) = v]. *)

(** {b NOTE} that the second parameter of the {!constructor:Patt}  constructor
    holds an array of terms. This is essential for variables binding: using an
    array of variables would NOT suffice. *)

(** {b NOTE} that the value of the {!field:arity} field  (of a rewriting rule)
    gives the number of arguments contained in its LHS. As a consequence,  the
    value of [r.arity] is always equal to [List.length r.lhs] and it gives the
    minimal number of arguments required to match the LHS of the rule. *)

(** The RHS (or action) or a rewriting rule is represented by a term, in which
    (higher-order) variables representing a "terms with environments" (see the
    {!type:term_env} type) are bound. To effectively apply the rewriting rule,
    these  bound variables must be substituted using "terms with environments"
    that are constructed when matching the LHS of the rule. *)

(** Representation of a "term with environment", which intuitively corresponds
    to a term with bound variables (or a "higher-order" term) represented with
    the {!constructor:TE_Some} constructor. Other constructors are included so
    that "terms with environments" can be bound in the RHS of rewriting rules.
    This is purely technical. *)
 and term_env =
  | TE_Vari of term_env Bindlib.var
  (** Free "term with environment" variable (used to build a RHS). *)
  | TE_Some of (term, term) Bindlib.mbinder
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

(** {3 Decision trees for rewriting} *)

(** Trees are used to efficiently choose a rewriting rule given a list of
    terms (beginning with a symbol) to be rewrote.  The left hand has side of
    the rule is spread across the {!cons:Node}s of the tree.  Hence,
    progressing down the tree is equivalent to reducing the set of possible
    rules.  When a {!cons:Leaf} is reached, the target is rewrote to the
    content of the leaf. *)
 and tree =
  | Leaf of int IntMap.t * int PosMap.t * (term_env, term) Bindlib.mbinder
  (** Holds the right hand side of a rule.  In a {!cons:Leaf}[(e, r, a)],
      - [a] is the right hand side of the rule.
      - [e] maps a position in the stack containing terms which stand as
            pattern variables in some rules to the slot allocated in the
            {!type:term_env array}.
      - [r] maps position in the remaining of the input stack to variable slot
            in the environment; the variables located by this mapping are not
            relevant regarding rule choice but are needed in the right hand
            side. *)
  | Node of node_data
  (** Nodes allow to perform switches, a switch being the matching of a
      pattern.  Briefly, a {!cons:Node} contains one subtree per possible
      switch, plus possibly a default case. *)
  | Fail

(** Data contained in a node of the tree.  {!recfield:switch} contains the
    term on which the switch that gave birth to this node has been performed.
    {!recfield:swap} indicates whether the columns of the matrix have been
    swapped before the switch and {!recfield:children} contains the
    subtrees. *)
 and node_data =
  { swap : int option
  (** Indicates on which term of the input stack (counting from the head), the
      next switch is to be done.
      XXX remove option?  *)
  ; push : bool
    (** Whether to push the current term into the stack containing
        variables. *)
  ; children : (term option * tree) list
  (** Subtrees resulting from either specialisation on terms or default case.
      First element is {!cons:None} if child is result of a default case or
      {!cons:Some}[(t)] if it results from specialisation on [t]. *) }

(** {3 Metavariables and related functions} *)

(** Representation of a metavariable,  which corresponds to a place-holder for
    a (yet unknown) term which free variables are bound by an environment. The
    substitution of the free variables with the environment is suspended until
    the metavariable is instantiated (i.e., set to a particular term).  When a
    metavariable [m] is instantiated,  the suspended substitution is  unlocked
    and terms of the form {!constructor:Meta}[(m,env)] can be unfolded. *)
 and meta =
  { meta_key   : int
  (** Unique key of the metavariable. *)
  ; meta_name  : string option
  (** Optional name. *)
  ; meta_type  : term ref
  (** Type of the metavariable. *)
  ; meta_arity : int
  (** Arity of the metavariable (environment size). *)
  ; meta_value : (term, term) Bindlib.mbinder option ref
  (** Definition of the metavariable, if known. *) }

(** [unfold t] repeatedly unfolds the definition of the surface constructor of
    [t], until a significant {!type:term} constructor is found.  The term that
    is returned cannot be an instantiated metavariable or term environment nor
    a reference cell ({!constructor:TRef} constructor). Note that the returned
    value is physically equal to [t] if no unfolding was performed. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Meta(m, ar)          ->
      begin
        match !(m.meta_value) with
        | None    -> t
        | Some(b) -> unfold (Bindlib.msubst b ar)
      end
  | TEnv(TE_Some(b), ar) -> unfold (Bindlib.msubst b ar)
  | TRef(r)              ->
      begin
        match !r with
        | None    -> t
        | Some(v) -> unfold v
      end
  | _                    -> t

(** {b NOTE} that {!val:unfold} must (almost) always be called before matching
    over a value of type {!type:term}. *)

(** [unset m] returns [true] if [m] is not instantiated. *)
let unset : meta -> bool = fun m -> !(m.meta_value) = None

(** [fresh_meta a n] creates a new metavariable of type [a] and arity [n]. *)
let fresh_meta : ?name:string -> term -> int -> meta =
  let counter = Pervasives.ref (-1) in
  let fresh_meta ?name a n =
   { meta_key =  Pervasives.(incr counter; !counter) ; meta_name = name
   ; meta_type = ref a ; meta_arity = n ; meta_value = ref None}
  in fresh_meta

(** [set_meta m v] sets the value of the metavariable [m] to [v]. Note that no
    specific check is performed, so this function may lead to cyclic terms. *)
let set_meta : meta -> (term, term) Bindlib.mbinder -> unit = fun m v ->
  m.meta_type := Kind (* to save memory *); m.meta_value := Some(v)

(** [internal m] returns [true] if [m] is unnamed (i.e., not user-defined). *)
let internal : meta -> bool = fun m -> m.meta_name = None

(** [meta_name m] returns a string representation of [m]. *)
let meta_name : meta -> string = fun m ->
  match m.meta_name with
  | Some(n) -> "?" ^ n
  | None    -> "?" ^ string_of_int m.meta_key

(** [term_of_meta m env] constructs the application of a dummy symbol with the
    same type as [m], to the element of the environment [env].  The idea is to
    obtain a term with the same type as {!constructor:Meta}[(m,env)], but that
    is simpler to type-check. *)
let term_of_meta : meta -> term array -> term = fun m e ->
  let s =
    { sym_name = Printf.sprintf "[%s]" (meta_name m)
    ; sym_type = ref !(m.meta_type) ; sym_path = [] ; sym_def = ref None
    ; sym_impl = []; sym_rules = ref [] ; sym_mode = Const
    ; sym_tree = ref Fail }
  in
  Array.fold_left (fun acc t -> Appl(acc,t)) (Symb(s, Alias("#"))) e

(** {b NOTE} that {!val:term_of_meta} relies on a dummy symbol and not a fresh
    variable to avoid polluting the context. *)

(** {3 Smart constructors and Bindlib infrastructure} *)

(** A short name for the binding of a term in a term. *)
type tbinder = (term, term) Bindlib.binder

(** A short name for the type of a free term variable. *)
type tvar = term Bindlib.var

(** A short name for the type of a term in a {!type:Bindlib.box}. *)
type tbox = term Bindlib.box

(** A short name for the type of a free {!type:term_env} variable. *)
type tevar = term_env Bindlib.var

(** A short name for the type of a boxed {!type:term_env}. *)
type tebox = term_env Bindlib.box

(** [mkfree x] injects the [Bindlib] variable [x] in a term. *)
let mkfree : tvar -> term = fun x -> Vari(x)

(** [te_mkfree x] injects the [Bindlib] variable [x] in a {!type:term_env}. *)
let te_mkfree : tevar -> term_env = fun x -> TE_Vari(x)

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
let _Symb : sym -> pp_hint -> tbox = fun s h ->
  Bindlib.box (Symb(s,h))

(** [_Appl t u] lifts an application node to the {!type:tbox} type given boxed
    terms [t] and [u]. *)
let _Appl : tbox -> tbox -> tbox =
  Bindlib.box_apply2 (fun t u -> Appl(t,u))

(** [_Prod a b] lifts a dependent product node to the {!type:tbox} type, given
    a boxed term [a] for the domain of the product, and a boxed binder [b] for
    its codomain. *)
let _Prod : tbox -> tbinder Bindlib.box -> tbox =
  Bindlib.box_apply2 (fun a b -> Prod(a,b))

let _Impl : tbox -> tbox -> tbox =
  let dummy = Bindlib.new_var mkfree "_" in
  fun a b -> _Prod a (Bindlib.bind_var dummy b)

(** [_Abst a t] lifts an abstraction node to the {!type:tbox}  type,  given  a
    boxed term [a] for the domain type, and a boxed binder [t]. *)
let _Abst : tbox -> tbinder Bindlib.box -> tbox =
  Bindlib.box_apply2 (fun a t -> Abst(a,t))

(** [_Meta m ar] lifts the metavariable [m] to the {!type:tbox} type given its
    environment [ar]. As for symbols in {!val:_Symb}, metavariables are closed
    objects so they do not require lifting. *)
let _Meta : meta -> tbox array -> tbox = fun u ar ->
  Bindlib.box_apply (fun ar -> Meta(u,ar)) (Bindlib.box_array ar)

(** [_Patt i n ar] lifts a pattern variable to the {!type:tbox} type. *)
let _Patt : int option -> string -> tbox array -> tbox = fun i n ar ->
  Bindlib.box_apply (fun ar -> Patt(i,n,ar)) (Bindlib.box_array ar)

(** [_TEnv te ar] lifts a term environment to the {!type:tbox} type. *)
let _TEnv : tebox -> tbox array -> tbox = fun te ar ->
  Bindlib.box_apply2 (fun te ar -> TEnv(te,ar)) te (Bindlib.box_array ar)

(** [_Wild] injects the constructor [Wild] into the {!type:tbox} type. *)
let _Wild : tbox = Bindlib.box Wild

(** [_TRef r] injects the constructor [TRef(r)] into the {!type:tbox} type. It
    should be the case that [!r] is [None]. *)
let _TRef : term option ref -> tbox = fun r ->
  Bindlib.box (TRef(r))

(** [lift t] lifts the {!type:term} [t] to the {!type:tbox} type. This has the
    effect of gathering its free variables, making them available for binding.
    Bound variable names are automatically updated in the process. *)
let rec lift : term -> tbox = fun t ->
  let lift_term_env te =
    match te with
    | TE_Vari(x) -> Bindlib.box_var x
    | _          -> Bindlib.box te (* closed objects *)
  in
  match unfold t with
  | Vari(x)     -> _Vari x
  | Type        -> _Type
  | Kind        -> _Kind
  | Symb(s,h)   -> _Symb s h
  | Prod(a,b)   -> _Prod (lift a) (Bindlib.box_binder lift b)
  | Abst(a,t)   -> _Abst (lift a) (Bindlib.box_binder lift t)
  | Appl(t,u)   -> _Appl (lift t) (lift u)
  | Meta(r,m)   -> _Meta r (Array.map lift m)
  | Patt(i,n,m) -> _Patt i n (Array.map lift m)
  | TEnv(te,m)  -> _TEnv (lift_term_env te) (Array.map lift m)
  | Wild        -> _Wild
  | TRef(r)     -> _TRef r

(** [cleanup t] builds a copy of the {!type:term} [t] where every instantiated
    metavariable,  instantiated term environment,  and reference cell has been
    eliminated using {!val:unfold}. Another effect of the function is that the
    the names of bound variables updated.  This is useful to avoid any form of
    "visual capture" while printing terms. *)
let cleanup : term -> term = fun t -> Bindlib.unbox (lift t)
