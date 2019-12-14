(** Source code position management.  This module may be used to map sequences
    of characters in a source file to an abstract syntax tree. *)

open Pacomb

(** Type of a position, corresponding to a continuous range of characters in a
    (utf8-encoded) source file. Elements of this type are (lazily) constructed
    by [Earley], using the following [locate] function. *)
type pos = Pos.interval

(* NOTE laziness is essential on big files (especially those with long lines),
   because computing utf8 positions is expensive. *)

(** Convenient short name for an optional position. *)
type popt = pos option

(** [equal_pos p1 p2] tells whether [p1] and [p2] denote the same location. *)
let equal_pos : pos -> pos -> bool = fun p1 p2 -> p1 = p2

(** [equal p1 p2] tells whether [p1] and [p2] denote the same position. *)
let equal : popt -> popt -> bool = fun p1 p2 ->
  match (p1, p2) with
  | (Some(p1), Some(p2)) -> equal_pos p1 p2
  | (None    , None    ) -> true
  | (_       , _       ) -> false

(** Type constructor extending a type (e.g. a piece of abstract syntax) with a
    a source code position. *)
type 'a loc =
  { elt : 'a   (** The element that is being localised.        *)
  ; pos : popt (** Position of the element in the source code. *) }

(** Localised string type (widely used). *)
type strloc = string loc

(** [make pos elt] associates the position [pos] to [elt]. *)
let make : popt -> 'a -> 'a loc =
  fun pos elt -> { elt ; pos }

(** [in_pos pos elt] associates the position [pos] to [elt]. *)
let in_pos : pos -> 'a -> 'a loc =
  fun p elt -> { elt ; pos = Some p }

(** [none elt] wraps [elt] in a ['a loc] structure without any specific source
    code position. *)
let none : 'a -> 'a loc =
  fun elt -> { elt ; pos = None }

(** [to_string pos] transforms [pos] into a readable string. *)
let to_string : pos -> string = fun p ->
  let open Pos in
  let { start = { name = fname; line = start_line; col = start_col ; _ }
      ; end_  = { line = end_line; col = end_col ; _ } } = p
  in
  let fname = match fname with
    | ""    -> ""
    | n -> n ^ ", "
  in
  if start_line <> end_line then
    Printf.sprintf "%s%d:%d-%d:%d" fname start_line start_col end_line end_col
  else if start_col = end_col then
    Printf.sprintf "%s%d:%d" fname start_line start_col
  else
    Printf.sprintf "%s%d:%d-%d" fname start_line start_col end_col

(** [print oc pos] prints the optional position [pos] to [oc]. *)
let print : Format.formatter -> pos option -> unit = fun ch p ->
  match p with
  | None    -> Format.pp_print_string ch "unknown location"
  | Some(p) -> Format.pp_print_string ch (to_string p)
