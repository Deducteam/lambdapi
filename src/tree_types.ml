(** Miscellaneous types and utilities for decision trees. *)
open Extra

(** {3 Tree constructors} *)

(** Define a simpler representation of terms. *)
module Treecons =
struct
  (** A constructor is the representation of a symbol along with the number of
      arguments to which it is applied. *)
  type t =
    | Symb of (int * string * Files.module_path)
    (** 1. Arity of the considered constructor.  A same symbol representation
           may generate several constructors with different arities.  For
           instance, with [g: N ⇒ N ⇒ N], [rule f g (g &x) → r] uses [g] with
           arity 1 and 2.
        2. Symbol of the constructor.
        3. Module name where the symbol of the constructor is defined. *)
    | Abst
    (** An abstraction*)
    | Vari of string
    (** A bound variable with a name. *)

  (** [pp o c] prints tree constructor [c] to output channel [o]. *)
  let pp : t pp = fun oc -> function
    | Abst          -> Format.fprintf oc "λ"
    | Vari(s)       -> Format.pp_print_string oc s
    | Symb(a, n, _) -> Format.fprintf oc "%s %d-ary" n a

  (** [compare c d] is a comparison function for constructors. *)
  let compare : t -> t -> int = Pervasives.compare
end

(** A mapping with {!type:Treecons.t} as keys. *)
module TcMap = Map.Make(Treecons)

(** {3 Decision trees for rewriting} *)

(** Data used to remap terms from lhs to rhs. *)
type 't binding_data = int * 't Bindlib.var array

(** Definition of a tree parametrised by
    - ['t] the terms in the tree,
    - ['r] the content of the leaves. *)
type ('t, 'r) tree =
  | Leaf of (int * 't binding_data) list * 'r
  (** Holds the right hand side of a rule.  In a {!constructor:Leaf}[(e, a)],
      - [e] maps positions in the stack containing terms which stand as
            pattern variables in some rules to the slot allocated in the
            {!type:term_env array}.  An associative list is used rather than a
            mapping because the only operations performed are adding elements
            and then {!val:List.iter}ing through the whole structure.
      - [a] is the right-hand side of the rule. *)
  | Node of ('t, 'r) node_data
  (** Nodes allow to perform switches, a switch being the matching of a
      pattern.  Briefly, a {!constructor:Node} contains one subtree per
      possible switch, plus possibly a default case and an abstraction
      case. *)
  | Condition of ('t, 'r) condition_data
  (** Binary node with branching depending on a boolean condition on a
      term. *)
  | Fail

(** Constraints among elements of the tree. *)
and 't tree_constraint =
  | TcstrEq of int * int
  (** [TcstrEq(i, j)] ensures that the terms at indexes [i] and [j] are
      convertible. *)
  | TcstrFreeVars of 't Bindlib.var array * int
  (** [TcstrFreeVars(v, i)] ensures the term at slot [i] of {!val:vars}
      contain only free variables that are in [v]. *)

(** Data needed to carry out a condition verification during evaluation. *)
and ('t, 'r) condition_data =
  { ok : ('t, 'r) tree
  (** Tree branched on if the condition is verified. *)
  ; condition : 't tree_constraint
  (** Type of the condition. *)
  ; fail : ('t, 'r) tree
  (** Tree branched on if the condition is not verified. *)}

(** Data contained in a node of a tree.  A node allows to filter the possible
    rules by branching on a child node. *)
and ('t, 'r) node_data =
  { swap : int
  (** Indicates on which term of the input stack (counting from the head), the
      next switch is to be done. *)
  ; store : bool
  (** Whether to store the current term.  Stored terms might be used in the
      right hand side. *)
  ; children : ('t, 'r) tree TcMap.t
  (** Subtrees that represent the matching of a constructor available in the
      rules.  Maps representation of constructors as strings built with
      {!val:add_args_repr} or {!val:symrepr_of_term} from {!module:dtree} to
      trees resulting from a specialisation on the key. *)
  ; abstraction : ('t Bindlib.var * ('t, 'r) tree) option
  (** Specialisation by an abstraction along with the free variable
      involved. *)
  ; default : ('t, 'r) tree option
  (** If a wildcard is among the patterns, this subtree is used when the term
      matched isn't a constructor among the {!field:children} terms. *)}

(** {3 Functions on trees} *)

(** [iter l n f t] is a generic iterator on trees; with
    - function [l] performed on leaves,
    - function [n] performed on nodes,
    - [f] returned in case of {!constructor:Fail} on tree [t]. *)
let tree_iter :
  do_leaf:((int * (int * 't Bindlib.var array)) list -> 'r -> 'a) ->
  do_node:(int -> bool -> 'a TcMap.t ->
           ('t Bindlib.var * 'a ) option -> 'a option -> 'a) ->
  do_condition:('a -> 't tree_constraint -> 'a -> 'a) ->
  fail:'a -> ('t, 'r) tree -> 'a =
  fun ~do_leaf ~do_node ~do_condition ~fail t ->
    let rec loop = function
      | Leaf(pa, a)                                 -> do_leaf pa a
      | Fail                                        -> fail
      | Condition(cdata)                            ->
          let { condition ; ok ; fail } = cdata in
          do_condition (loop ok) condition (loop fail)
      | Node({ swap ; store ; children ; abstraction ; default }) ->
          do_node swap store
            (TcMap.map loop children)
            (Option.map (fun (v, x) -> (v, loop x)) abstraction)
            (Option.map loop default) in
    loop t

(** [tree_capacity t] computes the capacity of tree [t]. During evaluation the
    terms that are being filtered by the patterns have to be saved in order to
    be bound in the right hand side of the rule, or because they must verify a
    constraint. The capacity is the maximum number of such terms that may need
    to be saved. More precisely, let [P] be the set of all paths from the root
    to leaves in the tree [t], and let [nb_store] be a function mapping a path
    to the number of nodes that have the {!field:store} tag to [true]. We then
    define the capacity [c] of [t] is [c = max{nb_store(p) | p ∈ P}]. *)
let tree_capacity : ('t, 'r) tree -> int = fun tr ->
  let do_leaf _ (_:'r) = 0 in
  let fail = 0 in
  let do_node _ st ch ab de =
    let _, chdepths = List.split (TcMap.bindings ch) in
    let dedepth = Option.get de 0 in
    let abdepth = match ab with Some(_, n) -> n | None -> 0 in
    List.max ~cmp:Int.compare (abdepth::dedepth::chdepths) +
    (if st then 1 else 0) in
  let do_condition t (_:'t tree_constraint) f = max t f in
  tree_iter ~do_leaf:do_leaf ~fail:fail ~do_node:do_node
    ~do_condition:do_condition tr

(** A tree with its capacity and as lazy structures.  For the definition of
    the capacity, see {!val:capacity}. *)
type ('t, 'r) dtree = int Lazy.t * ('t, 'r) tree Lazy.t

(** The empty decision tree. *)
let empty_dtree : ('t, 'r) dtree = lazy 0, lazy Fail
