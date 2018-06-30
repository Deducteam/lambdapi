(** Source code position management.  This module may be used to map sequences
    of characters in a source file to an abstract syntax tree. *)


(** Type of a position, corresponding to a continuous range of characters in a
    source file. Elements of this type are constructed by [Earley],  using the
    following [locate] function. *)
type pos =
  { start_buf : Input.buffer (** Buffer for the start position.   *)
  ; start_pos : int          (** Position for the start position. *)
  ; end_buf   : Input.buffer (** Buffer for the end position.     *)
  ; end_pos   : int          (** Position for the end position.   *) }

(** [locate buf1 pos1 buf2 pos2] builds a [pos] structure,  given two [Earley]
    input buffers. This function is used by Earley to generate the position of
    elements during parsing.
    @see <https://github.com/rlepigre/earley/> Earley *)
let locate : Input.buffer -> int -> Input.buffer -> int -> pos =
  fun buf1 pos1 buf2 pos2 ->
    {start_buf = buf1; start_pos = pos1; end_buf = buf2; end_pos = pos2}

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
  let open Printf in
  let fname =
    match Input.filename p.start_buf with
    | ""    -> ""
    | fname -> fname ^ ", "
  in
  let line1 = Input.line_num p.start_buf in
  let col1  = Input.utf8_col_num p.start_buf p.start_pos in
  let line2 = Input.line_num p.end_buf in
  let col2  = Input.utf8_col_num p.end_buf p.end_pos in
  if line1 <> line2 then sprintf "%s%d:%d-%d:%d" fname line1 col1 line2 col2
  else if col1 = col2 then sprintf "%s%d:%d" fname line1 col1
  else sprintf "%s%d:%d-%d" fname line1 col1 col2

(** [print oc pos] prints the optional position [pos] to [oc]. *)
let print : Format.formatter -> pos option -> unit = fun ch p ->
  match p with
  | None   -> Format.pp_print_string ch "unknown location"
  | Some p -> Format.pp_print_string ch (to_string p)
