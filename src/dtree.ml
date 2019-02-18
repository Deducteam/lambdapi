open Terms
open Timed
open Extra

(* TODO
   + define more clearly what is a constructor and what is not, i.e.  clarify
     what will the 'switches' be in the tree (in other word, what
     characterises a branch).
   + each rule has its arity
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
  (** Type used to describe a line of a matrix (either a column or a row). *)
  type line = term list

  (** Type of a matrix of patterns.  The type is changed (from rule list) as
      the matrix is made to be shrunk; keeping the rule list type would be
      deceitful semantically.  Each line is a row having an attached
      action. *)
  type t = (line * action) list

  (** [make r] creates  the  initial pattern  matrix from a  list of rewriting
      rules. *)
  let make : rule list -> t = List.map (fun r -> r.lhs, r.rhs)

  (** [get_col n m] retrieves column [n] of matrix [m].  There is some
      processing because all rows do not have the same length. *)
  let get_col : int -> t -> line = fun ind ->
    List.fold_left (fun acc (elt, _) ->
      if List.length elt > ind then List.nth elt ind :: acc else acc) []

  (** [specialize p m] specializes the matrix [m] when matching against pattern
      [p]. *)
      (* See the [matching] function of [eval] *)
  let specialize : term -> t -> t = fun p ->
    List.filter (fun (l, _) ->
        match p, List.hd l with
        | Symb(s, _), Symb(s', _)      -> s = s' (* Equality of records? *)
        | Abst(_, _), Abst(_, _)       -> failwith "abstraction NYI"
        | Patt(_, _, _), Patt(_, _, _) -> failwith "pattern NYI"
        | _ -> failwith "NYI")

  (** [default m] computes the default matrix containing what remains to be
      matched. *)
  let default : t -> t = fun m ->
    List.filter (fun (l, _) ->
        match List.hd l with
        | Symb(_, _)    -> false
        | Abst(_, _)    -> failwith "abstraction NYI"
        | Patt(_, _, _) -> failwith "patt NYI"
        | _             -> failwith "NYI _") m

  (** [cmp c d] compares columns [c] and [d] returning:  +1 if c > d, 0 if c =
      d or -1 if c < d; where <, = and > are defined according to a heuristic.
  *)
  let cmp : line -> line -> int = fun c d -> 0

  (** [pick_best m] returns the index of the best column of matrix [m]
      according to a heuristic. *)
  let pick_best : t -> int = fun m -> 0

  (** [discard_patt_free m] returns the list of indexes of columns containing
      terms that can be matched against (discard pattern-free columns). *)
  let discard_patt_free : t -> int array = fun m ->
    let rec matchable : line -> bool = function
      | [] -> false
      | x :: xs ->
        begin
          match x with
          | Symb(_, _) | Abst(_, _) | Patt(_, _, _) -> true
          | _ -> matchable xs
        end in
    let indexes = List.mapi (fun i (e, _) ->
        if matchable e then Some i else None) m in
    let remaining =
      List.fold_left (fun acc elt -> match elt with
          | Some i -> i :: acc
          | None -> acc) [] indexes in
    Array.of_list remaining

  (** [select m i] keeps the columns of [m] whose index are in [i]. *)
  let select : t -> int array -> t = fun m ->
    Array.fold_left (fun acc elt -> List.nth m elt :: acc) []
end

(** [grow m]  creates a pattern matching tree from the pattern matching matrix
    [m].  Counterpart of the compilation_scheme in Maranget's article. *)
let rec grow : Pattmat.t -> t = fun m ->
  if List.length m = 0 then (* If matrix is empty *)
    Fail else
    (* Look at the first line, if it contains only wildcards, then
       execute the associated action. *)
    let fline = fst @@ List.hd m in
    if fline = List.map (fun _ -> Wild) fline then
      Leaf(snd @@ List.hd m) else
      (* Pick a column in the matrix and pattern match on the constructors in
         it to grow the tree. *)
    let kept_cols = Pattmat.discard_patt_free m in
    let sel_in_partial = Pattmat.pick_best (Pattmat.select m kept_cols) in
    let swap = if kept_cols.(sel_in_partial) = 0
      then None else Some kept_cols.(sel_in_partial) in
    let selected_c = match swap with
      | None   -> Pattmat.get_col 0 m
      | Some i -> Pattmat.get_col i m in
    let syms = List.filter (fun x -> match x with
        | Symb(_, _) -> true
        | _          -> false) selected_c in
    let ms = List.map (fun s -> Pattmat.specialize s m) syms in
    let children = List.map grow (ms @ if is_sig syms
                                  then []
                                  else [Pattmat.default m]) in
    Node(swap, children)
(* TODO
   + what about vars and metavars -> this seem to concern the tree walk and
     matching the pattern, not the growth of the tree
*)
