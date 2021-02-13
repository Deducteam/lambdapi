(** Source code position management.  This module may be used to map sequences
    of characters in a source file to an abstract syntax tree. *)

(** Type of a position, corresponding to a continuous range of characters in a
    (utf8-encoded) source. *)
type pos =
  { fname      : string option (** File name for the position.       *)
  ; start_line : int (** Line number of the starting point.          *)
  ; start_col  : int (** Column number (utf8) of the starting point. *)
  ; end_line   : int (** Line number of the ending point.            *)
  ; end_col    : int (** Column number (utf8) of the ending point.   *) }

(** Convenient short name for an optional position. *)
type popt = pos option

(** [equal p1 p2] tells whether [p1] and [p2] denote the same position. *)
let equal : popt -> popt -> bool = fun p1 p2 ->
  match (p1, p2) with
  | (Some(p1), Some(p2)) -> p1 = p2
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

(** [end_pos po] creates a position from the end of position [po]. *)
let end_pos : popt -> popt = fun po ->
  match po with
  | None -> None
  | Some p ->
    Some { p with start_line = p.end_line; start_col = p.end_line }

(** [none elt] wraps [elt] in a ['a loc] structure without any specific source
    code position. *)
let none : 'a -> 'a loc =
  fun elt -> { elt ; pos = None }

(** [cat p1 p2] is the concatenation of positon [p1] and [p2]. If [p1] and
    [p2] have different filenames, the resulting filename is [None]. *)
let cat : pos -> pos -> pos = fun p1 p2 ->
  { fname =
      if p1.fname <> p2.fname then invalid_arg "Pos.cat: filename mismatch"
      else p1.fname
  ; start_line = p1.start_line
  ; start_col = p1.start_col
  ; end_line = p2.end_line
  ; end_col = p2.end_col }

(** [to_string ?print_fname pos] transforms [pos] into a readable string. If
    [print_fname] is [true] (the default), the filename contained in [pos] is
    printed. *)
let to_string : ?print_fname:bool -> pos -> string =
  fun ?(print_fname=true) {fname; start_line; start_col; end_line; end_col} ->
  let fname =
    if not print_fname then "" else
    match fname with
    | None    -> ""
    | Some(n) -> n ^ ", "
  in
  if start_line <> end_line then
    Printf.sprintf "%s%d:%d-%d:%d" fname start_line start_col end_line end_col
  else if start_col = end_col then
    Printf.sprintf "%s%d:%d" fname start_line start_col
  else
    Printf.sprintf "%s%d:%d-%d" fname start_line start_col end_col

(** [pp ppf pos] prints the optional position [pos] on [ppf]. *)
let pp : popt Lplib.Base.pp = fun ppf p ->
  match p with
  | None    -> Format.pp_print_string ppf "unknown location"
  | Some(p) -> Format.pp_print_string ppf (to_string p)

(** [pp_short ppf pos] prints the optional position [pos] on [ppf]. *)
let pp_short : popt Lplib.Base.pp = fun ppf p ->
  match p with
  | None    -> Format.pp_print_string ppf "unknown location"
  | Some(p) -> let print_fname=false in
               Format.pp_print_string ppf (to_string ~print_fname p)

(** [map f loc] applies function [f] on the value of [loc] and keeps the
    position unchanged. *)
let map : ('a -> 'b) -> 'a loc -> 'b loc = fun f loc ->
  {loc with elt = f loc.elt}

(** [locate ?fname loc] converts the pair of position [loc] and filename
    [fname] of the Lexing library into a {!type:pos}. *)
let locate : ?fname:string -> Lexing.position * Lexing.position -> pos =
  fun ?fname (p1, p2) ->
  let fname = if p1.pos_fname = "" then fname else Some(p1.pos_fname) in
  let start_line = p1.pos_lnum in
  let start_col = p1.pos_cnum - p1.pos_bol in
  let end_line = p2.pos_lnum in
  let end_col = p2.pos_cnum - p2.pos_bol in
 {fname; start_line; start_col; end_line; end_col}
