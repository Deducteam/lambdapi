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
      | Abst
      (** Abstraction (no arguments, patterns are in β-normal form). *)
      | Vari of string
      (** A bound variable represented using a name. *)

    (** {b NOTE} the effective arity carried by the representation of a symbol
        is specific to a given symbol instance. Indeed, a symbol (in the sense
        of {!type:Terms.sym}) may lead to several constructors, with different
        effective arities. In the pattern “f g (g &x)” for example, symbol [g]
        is used with arity 0 (first occurence) and 1 (second occurence). *)

    (** [pp oc c] prints tree constructor [c] to output channel [o]. *)
    let pp : t pp = fun oc c ->
      match c with
      | Abst        -> Format.fprintf oc "λ"
      | Vari(s)     -> Format.pp_print_string oc s
      | Symb(a,s,_) -> Format.fprintf oc "%s %d-ary" s a

    (** [compare c1 c2] implements a total order on constructors. *)
    let compare : t -> t -> int = Pervasives.compare
  end

(** A mapping with atomic pattern constructors as keys. *)
module TCMap = Map.Make(TC)

(** {3 Decision trees for rewriting} *)

(** Constraints among elements of a decision tree. *)
type 'term tree_constraint =
  | Constr_Eq of int * int
  (** The terms at the given indices must be convertible. *)
  | Constr_FV of 'term Bindlib.var array * int
  (** The free variables of the term at given index should be in the array. *)

(** Representation of a tree. The definition relies on parameters since module
    {!module:Terms} depends on the current module, and that would thus produce
    a dependency cycle. However it should be understood that parameter [`term]
    will only be instantiated with [Terms.term] and parameter [`rhs] will only
    only be instantiated  with  [(Terms.term_env, Terms.term) Bindlib.mbinder]
    (i.e., the representation of a RHS). *)
type ('term, 'rhs) tree =
  | Fail
  (** Empty decision tree, used when there are no rewriting rules. *)
  | Leaf of (int * (int * 'term Bindlib.mvar)) list * 'rhs
  (** The value [Leaf(m, rhs)] stores the RHS [rhs] of the rewriting rule that
      can be applied upon reaching the leaf.  The association list [m] is used
      to construct the environment of the RHS. Note that we do not need to use
      a map here since we only need to insert at the head, an iterate over the
      elements of the structure. *)
  | Cond of
      { ok   : ('term, 'rhs) tree
      (** Branch to follow if the condition is verified. *)
      ; cond : 'term tree_constraint
      (** The condition to test. *)
      ; fail : ('term, 'rhs) tree
      (** Branch to follow if the condition is not verified. *) }
  (** Conditional branching according to a condition. *)
  | Node of
      { swap : int
      (** Indicates on which term of the input stack (counting from the head),
          the next switch is to be done. *)
      ; store : bool
      (** Whether to store the current term. Stored terms might be used in the
          right hand side. *)
      ; children : ('term, 'rhs) tree TCMap.t
      (** Subtrees representing the matching of available constructors. *)
      ; abstraction : ('term Bindlib.var * ('term, 'rhs) tree) option
      (** Specialisation by an abstraction with the involved free variable. *)
      ; default : ('term, 'rhs) tree option
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
let rec tree_capacity : ('t, 'r) tree -> int = fun tr ->
  match tr with
  | Leaf(_,_)  | Fail   -> 0
  | Cond({ok; fail; _}) -> max (tree_capacity ok) (tree_capacity fail)
  | Node({store; children=ch; abstraction=abs; default; _}) ->
      let c_ch = TCMap.fold (fun _ t m -> max m (tree_capacity t)) ch 0 in
      let c_default = Option.map_default tree_capacity 0 default in
      let c_abs = Option.map_default (fun (_,t) -> tree_capacity t) 0 abs in
      let c = max c_ch (max c_default c_abs) in
      if store then c + 1 else c

(** A tree with its capacity and as lazy structures.  For the definition of
    the capacity, see {!val:capacity}. *)
type ('term, 'rhs) dtree = int Lazy.t * ('term, 'rhs) tree Lazy.t

(** [empty_dtree] is the empty decision tree. *)
let empty_dtree : ('term, 'rhs) dtree = (lazy 0, lazy Fail)
