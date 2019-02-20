open Terms
open Extra

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

(** [iter l n f t] is a generic iterator on trees; with function [l] performed
    on leaves, function [n] performed on nodes, [f] returned in case of
    {!const:Fail} on tree [t]. *)
let iter : (action -> 'a) -> (int option -> 'a list -> 'a) ->
  'a -> t -> 'a = fun do_leaf do_node fail t ->
  let rec loop = function
    | Leaf(a)     -> do_leaf a
    | Fail        -> fail
    | Node(io, c) -> do_node io (List.map loop c) in
  loop t

(** [count_nodes t] counts the number of nodes (leaves are not counted) in
    [t]. *)
let count_nodes : t -> int =
  iter (fun _ -> 0) (fun _ c -> 1 + (List.fold_left (+) 0 c)) 0

(** [to_dot f t] creates a dot graphviz file [f].gv for tree [t]. *)
let to_dot : string -> t -> unit = fun fname tree ->
  let ochan = open_out (fname ^ ".gv") in
  let nodecount = ref 0 in
  Printf.fprintf ochan "graph {\n";
  (* We cannot use iter since we need the father to be passed. *)
  let rec write_tree : int -> t -> unit = fun father_l tree ->
    match tree with
    | Leaf(_)    ->
      begin
        incr nodecount ;
        Printf.fprintf ochan "\t%d -- %d [label=%s];\n" father_l
          !nodecount "l";
      end
    | Node(os, c) ->
      begin
        incr nodecount ;
        let tag = !nodecount in
        let label = match os with
          | None -> 0
          | Some i -> i in
        Printf.fprintf ochan "\t%d -- %d [label=%d];\n"
          father_l !nodecount label;
        List.iter (fun e -> write_tree tag e) c ;
      end
    | Fail        ->
      begin
        incr nodecount ;
        Printf.fprintf ochan "\t%d -- %d [label=%s];\n" father_l
          !nodecount "f";
        end
  in
  write_tree 0 tree ;
  Printf.fprintf ochan "}\n" ;
  close_out ochan

module Pattmat =
struct
  (** Type used to describe a line of a matrix (either a column or a row). *)
  type line = term list

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t = (line * action) list

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : rule list -> t = List.map (fun r -> r.lhs, r.rhs)

  (** [get_col n m] retrieves column [n] of matrix [m].  There is some
      processing because all rows do not have the same length. *)
  let get_col : int -> t -> line = fun ind ->
    List.fold_left (fun acc (elt, _) ->
      if List.length elt > ind then List.nth elt ind :: acc else acc) []

  (** [select m i] keeps the columns of [m] whose index are in [i]. *)
  let select : t -> int array -> t = fun m ->
    Array.fold_left (fun acc elt -> List.nth m elt :: acc) []

  (** [cmp c d] compares columns [c] and [d] returning:  +1 if c > d, 0 if c =
      d or -1 if c < d; where <, = and > are defined according to a heuristic.
  *)
  let cmp : line -> line -> int = fun _ _ -> 0

  (** [pick_best m] returns the index of the best column of matrix [m]
      according to a heuristic. *)
  let pick_best : t -> int = fun _ -> 0

  (** [pattern_free l] returns whether a line contains patterns or not.
      Typically, a line full of wildcards is pattern free. *)
  let rec pattern_free : line -> bool = function
    | []      -> true
    | x :: xs ->
      begin
        match x with
        (* Wildcards as Patt(None, _, _). *)
        | Patt(None, _, [||]) -> pattern_free xs
        (* The condition might be too restrictive. *)
        | _                   -> false
      end

  (** [discard_patt_free m] returns the list of indexes of columns containing
      terms that can be matched against (discard pattern-free columns). *)
  let discard_patt_free : t -> int array = fun m ->
    let indexes = List.mapi (fun i (e, _) ->
        if not (pattern_free e) then Some i else None) m in
    let remaining =
      List.fold_left (fun acc elt -> match elt with
          | Some i -> i :: acc
          | None -> acc) [] indexes in
    assert ((List.length remaining) > 0) ;
    Array.of_list remaining
end

let print_arr_int arr =
  Printf.printf "[" ;
  let rec loop = function
    | [] -> Printf.printf "]\n"
    | x :: xs -> Printf.printf "; %d" x ; loop xs
  in
  loop ( Array.to_list arr )
