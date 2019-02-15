open Terms
open Timed
open Extra

(* TODO
   define more clearly what is a constructor and what is not, i.e.  clarify
   what will the 'switches' be in the tree (in other word, what characterises
   a branch).
*)

(** Type of the leaves of the tree.  See {!file:terms.ml}, {!recfield:rhs}. *)
type action = (term_env, term) Bindlib.mbinder

(** Tree type.  Leaves are the targets of the rewriting, i.e. when a leaf is
    reached,  the  matched  pattern  is  rewrote  to  the  the  leaf.  The
    {!const:Node}[(i, t)] constructor allows to perform a switch among the
    subtrees in [t] while the [i] option allows to choose on which term of the
    stack the matching is to be done.  {!const:Fail} is a matching failure. *)
type t = Leaf of action
       | Node of int option * t list
       | Fail

(** [is_sig s] returns whether the list of symbols [s] contains a
    signature. *)
let is_sig : term list -> bool = fun r ->
  let symofterms = List.map
      (fun s -> match s with Symb(s', _) -> s' | _ -> assert false)
      (List.filter (fun x -> match x with
      | Symb(_, _) -> true | _ -> false) r) in
  let op_sym = List.map_find (fun x -> match x with
      | Symb(s, _) -> Some s
      | _          -> None) r in
  let a_sym = match op_sym with
    | Some s -> s
    | None -> failwith "no symbol found" in
  let sign = Files.PathMap.find a_sym.sym_path !Sign.loaded in
  let sign_sym = StrMap.map fst !(sign.sign_symbols) in
  let count = StrMap.fold (fun _ s acc ->
      if List.mem s symofterms then succ acc else acc) sign_sym 0 in
  count = StrMap.cardinal sign_sym

module Pattmat =
struct
  (** Type of a matrix of patterns.  The type is changed (from rule list) as the
      matrix is made to be shrunk; keeping the rule list type would be
      deceitful semantically. *)
  type t = (term list * action) list

  (** Type used to describe a column of a matrix. *)
  type column = term list

  (** [make r] creates  the  initial pattern  matrix from a  list of rewriting
      rules. *)
  let make : rule list -> t = List.map (fun r -> r.lhs, r.rhs)

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
  let select : t -> int list -> t = fun m indexes -> m
end

(** [grow m]  creates a pattern matching tree from the pattern matching matrix
    [m].  Counterpart of the compilation_scheme in Maranget's article. *)
let rec grow : Pattmat.t -> t = fun m ->
  if List.length m = 0 then Fail else
    let fline = fst @@ List.hd m in
    if fline = List.map (fun _ -> Wild) fline then
      Leaf(snd @@ List.hd m) else
    let cols = Pattmat.filter_on_cons m in
    let selected = Pattmat.pick_best (Pattmat.select m cols) in
    let syms = List.filter (fun x -> match x with
        | Symb(_, _) -> true
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
   + what about vars and metavars -> this seem to concern
     the tree walk and matching the pattern, not the growing of
     the tree
*)
