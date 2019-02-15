open Terms
open Timed

(* TODO
   define more clearly what is a constructor and what is not, i.e.  clarify
   what will the 'switches' be in the tree (in other word, what characterises
   a branch).
*)

(** Tree type.  Leaves are the targets of the rewriting, i.e. when a leaf is
    reached, the matched pattern is rewrote to the the leaf.  The
    {!const:Node}[(i, t)] constructor allows to perform a switch among the
    subtrees in [t] while the [i] option allows to choose on which term of the
    stack the matching is to be done. *)
type t = Leaf of (term_env, term) Bindlib.mbinder
       | Node of int option * t list

(** [is_sig s] returns whether the list of symbols [s] contains a
    signature. *)
let is_sig : term list -> bool = fun tes -> false

module Pattmat =
struct
  (** Type of a matrix of patterns *)
  type t = term list array

  (** Type used to describe a column of a matrix. *)
  type column = term list

  (** [make r] creates  the  initial pattern  matrix from a  list of rewriting
      rules. *)
  let make : rule list -> t = fun rs ->
    [| [ Patt(None, "", [||]) ] |]

  (** [specialize t m] specializes the matrix [m] when matching against term
      [t]. *)
  let specialize : term -> t -> t = fun te m -> m

  (** [default m] computes the default matrix containing what remains to be
      matched. *)
  let default : t -> t = fun m -> m

  (** [cmp c d] compares columns [c] and [d] returning:  +1 if c > d, 0 if c =
      d or -1 if c < d; where <, = and > are defined according to a heuristic.
  *)
  let cmp : column -> column -> int = fun c d -> 0

  (** [pick_best m] returns the best column of matrix [m] according to a
      heuristic. *)
  let pick_best : t -> column = fun m -> []

  (** [filter_on_cons m] returns the list of indexes of columns which contain
      at least one constructor. *)
  let filter_on_cons : t -> int list = fun m -> []

  (** [select m i] keeps the columns of [m] whose index are in i. *)
  let select : t -> int list -> t = fun m indexes -> [| |]
end

(** [grow m] creates a pattern matching tree from the pattern matching
    matrix [m]. *)
let rec grow : Pattmat.t -> t = fun m ->
  let cols = Pattmat.filter_on_cons m in
  let selected = Pattmat.pick_best (Pattmat.select m cols) in
  let syms = List.filter (fun x -> match x with
        Symb(_, _) -> true
      | _          -> false) selected in
  let rec specmats : term list -> Pattmat.t list = function
    | []    -> []
    | s::ss -> Pattmat.specialize s m::specmats ss in
  let ms = specmats syms in
  let children = List.map grow (ms @ if is_sig syms
                                     then []
                                     else [Pattmat.default m]) in
  Node(None, children)
(* TODO
   + termination? leaves are never created,
   + what about vars and metavars
*)
