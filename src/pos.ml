(** Source code position management.  This module may be used to map sequences
    of characters in a source file to an abstract syntax tree. *)


(** Type of a position, corresponding to a continuous range of characters in a
    (utf8 encoded) source file. For denoting a zero-length position is to have
    [end_col] equal to [start_col - 1]. *)
type pos =
  { fname       : string option (** File name for the position.       *)
  ; start_line  : int (** Line number of the starting point.          *)
  ; start_col   : int (** Column number (utf8) of the starting point. *)
  ; end_line    : int (** Line number of the ending point.            *)
  ; end_col     : int (** Column number (utf8) of the ending point.   *) }

(** Convenient short name for an optional position. *)
type popt = pos option

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
  let fname =
    match p.fname with
    | None       -> ""
    | Some fname -> Printf.sprintf "%s, " fname
  in
  if p.start_line <> p.end_line then
    Printf.sprintf "%s%d:%d-%d:%d" fname
      p.start_line p.start_col p.end_line p.end_col
  else if p.start_col = p.end_col then
    Printf.sprintf "%s%d:%d" fname p.start_line p.start_col
  else
    Printf.sprintf "%s%d:%d-%d" fname p.start_line p.start_col p.end_col

(** [print oc pos] prints the optional position [pos] to [oc]. *)
let print : Format.formatter -> pos option -> unit = fun ch p ->
  match p with
  | None   -> Format.pp_print_string ch "unknown location"
  | Some p -> Format.pp_print_string ch (to_string p)

open Input

(** [locate buf1 pos1 buf2 pos2] builds a position structure, given two Earley
    input buffers. This function is used by Earley to generate the position of
    elements during parsing.
    @see <https://github.com/rlepigre/earley/> Earley *)
let locate : buffer -> int -> buffer -> int -> pos =
  fun buf1 pos1 buf2 pos2 ->
    let fname =
      match filename buf1 with
      | ""    -> None
      | fname -> Some fname
    in
    let start_line = line_num buf1 in
    let end_line   = line_num buf2 in
    let start_col  = utf8_col_num buf1 pos1 in
    let end_col    = utf8_col_num buf2 pos2 in
    { fname ; start_line ; start_col ; end_line ; end_col }
