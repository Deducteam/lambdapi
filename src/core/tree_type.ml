(** Miscellaneous types and utilities for decision trees. *)

open Lplib
open Lplib.Base
open Common

(** {3 Atomic pattern constructor representation} *)

(** Representation of an atomic pattern constructor. *)
module TC =
  struct
    (** Atomic pattern constructor. Term are identified by these constructors
        in the  trees. During  matching (in {!val:Eval.tree_walk}),  terms are
        transformed into these constructors to get the right sub-tree. *)
    type t =
      | Symb of Path.t * string * int
      (** Symbol identified by a fully qualified name (module path and name)
          and its arity in the pattern. *)
      | Vari of int
      (** A bound  variable identified by a ({e  branch}-wise) unique integer.
          These variables  are used with  a bidirectional map  (implemented as
          two maps) to  a higher order (Bindlib) variable. They  are also used
          in the environment builder to refer  to the higher order variables a
          term may depend on. *)

    (** {b NOTE} the effective arity carried by the representation of a symbol
        is specific to a given symbol instance. Indeed, a symbol (in the sense
        of {!type:Term.sym}) may lead to several constructors, with different
        effective arities. In the pattern “f g (g $x)” for example, symbol [g]
        is used with arity 0 (first occurence) and 1 (second occurence). *)

    (** [pp oc c] prints tree constructor [c] to output channel [o]. *)
    let pp : t pp = fun oc c ->
      match c with
      | Vari(d)     -> Format.pp_print_int oc d
      | Symb(_,s,a) -> Format.fprintf oc "%s %d-ary" s a

    (** [compare c1 c2] implements a total order on constructors. *)
    let compare : t -> t -> int = Stdlib.compare
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
  | CondFV of int * int array
  (** Are the (indexed) bound variables (which are free at the time of the
      checking) of the term at the given index in the array? *)

(** {!b NOTE} that when performing a {!constructor:tree_cond.CondFV} check, we
    are concerned about variables that were bound in the term being reduced
    and that may appear free while deconstructing it.  If the term being
    reduced contains free variables, those can appear in a subterm even if not
    in the array. *)

let pp_tree_cond : tree_cond pp = fun ppf tc ->
  match tc with
  | CondNL(i, j) -> Format.fprintf ppf "Nl(%d, %d)" i j
  | CondFV(i, _) -> Format.fprintf ppf "Fv(%d)" i

(** Representation of a tree. The definition relies on parameters since module
    {!module:Term} depends on the current module, and that would thus produce
    a dependency cycle. However it should be understood that parameter [`rhs]
    will only be instantiated with
    [(Term.term_env, Term.term) Bindlib.mbinder] (i.e., the representation
    of a RHS). *)
type 'rhs tree =
  | Fail
  (** Empty decision tree, used when there are no rewriting rules. *)
  | Leaf of (int * (int * int array)) list * 'rhs
  (** The value [Leaf(m, rhs)] stores the RHS [rhs] of the rewriting rule that
      can be applied upon reaching the  leaf. The association list [m] is used
      to construct the environment of the RHS. Note that we do not need to use
      a map here  since we only need  to insert at the head,  and iterate over
      the elements of the structure. Triplet  [(p, (v, xs))] of [m] means that
      when a rule  matches, the term to  be used as the [v]th  variable of the
      RHS  is found  in position  [p] in  the array  containing all  the terms
      gathered during  matching. The pattern  may have an environment  made of
      variables [xs]. The  integer [x] indicates the number  of meta variables
      to generate to replace the extra variables of the RHS. *)
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
      ; product : (int * 'rhs tree) option
      (** Specialisation by product with the involved free variable. *)
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
  | Leaf(_)  | Fail     -> 0
  | Eos(l,r)            -> max (tree_capacity l) (tree_capacity r)
  | Cond({ok; fail; _}) -> max (tree_capacity ok) (tree_capacity fail)
  | Node(r)             ->
      let c_ch =
        TCMap.fold (fun _ t m -> max m (tree_capacity t)) r.children 0
      in
      let c_default = Option.map_default tree_capacity 0 r.default in
      let c_abs =
        Option.map_default (fun (_,t) -> tree_capacity t) 0 r.abstraction
      in
      let c_prod =
        Option.map_default (fun (_,t) -> tree_capacity t) 0 r.product
      in
      let c = List.max [c_ch; c_default; c_abs; c_prod] in
      if r.store then c + 1 else c

(** A tree with its capacity and as lazy structures.  For the definition of
    the capacity, see {!val:capacity}.  Laziness allows to (sometimes) avoid
    creating several times the same trees when the rules are not given in one
    go. *)
type 'rhs dtree = int Lazy.t * 'rhs tree Lazy.t

(** [empty_dtree] is the empty decision tree. *)
let empty_dtree : 'rhs dtree = (lazy 0, lazy Fail)
