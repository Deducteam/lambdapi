(** Miscellaneous types and utilities for decision trees. *)

open Extra

(** {3 Atomic pattern constructor representation} *)

(** Representation of an atomic pattern constructor. *)
module TC =
  struct
    (** Atomic pattern constructor. *)
    type t =
      | Symb of int * string * Files.module_path
      (** Symbol with its effective arity, name and module path. *)
      | Vari of int
      (** A bound variable identified by a ({e branch}-wise) unique
          integer. *)

    (** {b NOTE} the effective arity carried by the representation of a symbol
        is specific to a given symbol instance. Indeed, a symbol (in the sense
        of {!type:Terms.sym}) may lead to several constructors, with different
        effective arities. In the pattern “f g (g &x)” for example, symbol [g]
        is used with arity 0 (first occurence) and 1 (second occurence). *)

    (** [pp oc c] prints tree constructor [c] to output channel [o]. *)
    let pp : t pp = fun oc c ->
      match c with
      | Vari(d)     -> Format.pp_print_int oc d
      | Symb(a,s,_) -> Format.fprintf oc "%s %d-ary" s a

    (** [compare c1 c2] implements a total order on constructors. *)
    let compare : t -> t -> int = Pervasives.compare
  end

(** A mapping with atomic pattern constructors as keys. *)
module TCMap = Map.Make(TC)

(** {3 Decision trees for rewriting} *)

(** Representation of a branching conditions. *)
type tree_cond =
  | CondNL of int * int
  (** Are the terms at the given indices convertible? We enforce the invariant
      that the first element is a point of reference, which appears in all the
      convertibility conditions involving a given non-linear variable. *)
  | CondFV of int array * int
  (** Are the (indexed) bound variables (which are free at the time of the
      checking) of the term at the given index in the array? *)

(** {!b NOTE} that when performing a {!constructor:tree_cond.CondFV} check, we
    are concerned about variables that were bound in the term being reduced
    and that may appear free while deconstructing it.  If the term being
    reduced contains free variables, those can appear in a subterm even if not
    in the array. *)

(** Representation of a tree. The definition relies on parameters since module
    {!module:Terms} depends on the current module, and that would thus produce
    a dependency cycle. However it should be understood that parameter [`rhs]
    will only be instantiated with
    [(Terms.term_env, Terms.term) Bindlib.mbinder] (i.e., the representation
    of a RHS). *)
type 'rhs tree =
  | Fail
  (** Empty decision tree, used when there are no rewriting rules. *)
  | Leaf of (int * (int * int array)) list * 'rhs
  (** The value [Leaf(m, rhs)] stores the RHS [rhs] of the rewriting rule that
      can be applied upon reaching the leaf.  The association list [m] is used
      to construct the environment of the RHS. Note that we do not need to use
      a map here since we only need to insert at the head, and iterate over
      the elements of the structure. *)
  | Cond of
      { ok   : 'rhs tree
      (** Branch to follow if the condition is verified. *)
      ; cond : tree_cond
      (** The condition to test. *)
      ; fail : 'rhs tree
      (** Branch to follow if the condition is not verified. *) }
  (** Conditional branching according to a condition. *)
  | Eos of 'rhs tree * 'rhs tree
  (** End of stack node, branches on left tree if the stack is finished, on
      the right if it isn't.  Required when there are rules with a lower arity
      than some other rule above and when {!val:Tree.rule_order} is set. *)
  | Node of
      { swap : int
      (** Indicates on which term of the input stack (counting from the head),
          the next switch is to be done. *)
      ; store : bool
      (** Whether to store the current term. Stored terms might be used in the
          right hand side, are for constraint checks. *)
      ; children : 'rhs tree TCMap.t
      (** Subtrees representing the matching of available constructors. *)
      ; abstraction : (int * 'rhs tree) option
      (** Specialisation by an abstraction with the involved free variable. *)
      ; default : 'rhs tree option
      (** When the available patterns contain a wildcard, this subtree is used
          as a last resort (if none of the {!field:children} match). *) }
  (** Arbitrarily branching node allowing to perform switches (a switch is the
      matching of a pattern). The node contains one subtree per switch, plus a
      possible default case as well as an abstraction case. *)

(** [tree_capacity t] computes the capacity of tree [t]. During evaluation the
    terms that are being filtered by the patterns have to be saved in order to
    be bound in the right hand side of the rule, or because they must verify a
    constraint. The capacity is the maximum number of such terms that may need
    to be saved. More precisely, let [P] be the set of all paths from the root
    to leaves in the tree [t], and let [nb_store] be a function mapping a path
    to the number of nodes that have the {!field:store} tag to [true]. We then
    define the capacity [c] of [t] is [c = max{nb_store(p) | p ∈ P}]. *)
let rec tree_capacity : 'r tree -> int = fun tr ->
  match tr with
  | Leaf(_,_)  | Fail   -> 0
  | Eos(l,r)            -> max (tree_capacity l) (tree_capacity r)
  | Cond({ok; fail; _}) -> max (tree_capacity ok) (tree_capacity fail)
  | Node({store; children=ch; abstraction=abs; default; _}) ->
      let c_ch = TCMap.fold (fun _ t m -> max m (tree_capacity t)) ch 0 in
      let c_default = Option.map_default tree_capacity 0 default in
      let c_abs = Option.map_default (fun (_,t) -> tree_capacity t) 0 abs in
      let c = max c_ch (max c_default c_abs) in
      if store then c + 1 else c

(** A tree with its capacity and as lazy structures.  For the definition of
    the capacity, see {!val:capacity}.  Laziness allows to (sometimes) avoid
    creating several times the same trees when the rules are not given in one
    go. *)
type 'rhs dtree = int Lazy.t * 'rhs tree Lazy.t

(** [empty_dtree] is the empty decision tree. *)
let empty_dtree : 'rhs dtree = (lazy 0, lazy Fail)
