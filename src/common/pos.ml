(** Positions in Lambdapi files. *)

open Lplib open Base

(** Type of a position, corresponding to a continuous range of characters in a
    (utf8-encoded) source. *)
type pos =
  { fname      : string option (** File name for the position.       *)
  ; start_line : int (** Line number of the starting point.          *)
  ; start_col  : int (** Column number (utf8) of the starting point. *)
  ; end_line   : int (** Line number of the ending point.            *)
  ; end_col    : int (** Column number (utf8) of the ending point.   *) }

(** Total comparison function on pos. *)
let cmp : pos cmp = fun p1 p2 ->
  let cmp = Int.compare in
  lex3 cmp cmp (lex3 (Option.cmp String.compare) cmp cmp)
    (p1.start_line, p1.start_col, (p1.fname, p1.end_line, p1.end_col))
    (p2.start_line, p2.start_col, (p2.fname, p2.end_line, p2.end_col))

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
let make : popt -> 'a -> 'a loc = fun pos elt -> { elt ; pos }

(** [none elt] wraps [elt] in a ['a loc] structure without any specific source
    code position. *)
let none : 'a -> 'a loc = fun elt -> make None elt

(** [in_pos pos elt] associates the position [pos] to [elt]. *)
let in_pos : pos -> 'a -> 'a loc = fun p elt -> make (Some p) elt

(** [end_pos po] creates a position from the end of position [po]. *)
let end_pos : popt -> popt = fun po ->
  match po with
  | None -> None
  | Some p -> Some {p with start_line = p.end_line; start_col = p.end_col}

(** [cat p1 p2] returns a position starting from [p1] start and ending with
   [p2] end. [p1] and [p2] must have the same filename. *)
let cat : pos -> pos -> pos = fun p1 p2 ->
  { fname = p2.fname
    (*FIXME: temporary fix for
      https://github.com/Deducteam/lambdapi/issues/1001
      if p1.fname <> p2.fname then invalid_arg __LOC__ else p1.fname*)
  ; start_line = p1.start_line
  ; start_col = p1.start_col
  ; end_line = p2.end_line
  ; end_col = p2.end_col }

let cat : popt -> popt -> popt = fun p1 p2 ->
  match p1, p2 with
  | Some p1, Some p2 -> Some (cat p1 p2)
  | Some p, None
  | None, Some p -> Some p
  | None, None -> None

(** [shift k p] returns a position that is [k] characters after [p]. *)
let shift : int -> popt -> popt = fun k p ->
  match p with
  | None -> assert false
  | Some ({start_col; _} as p) -> Some {p with start_col = start_col + k}

let after = shift 1
let before = shift (-1)

(** [to_string ?print_fname pos] transforms [pos] into a readable string. If
    [print_fname] is [true] (the default), the filename contained in [pos] is
    printed. *)
let to_string : ?print_fname:bool -> pos -> string =
  fun ?(print_fname=true) {fname; start_line; start_col; end_line; end_col} ->
  let fname =
    if not print_fname then "" else
    match fname with
    | None    -> ""
    | Some(n) -> n ^ ":"
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
  | None    -> string ppf "unknown location"
  | Some(p) -> string ppf (to_string p)

(** [short ppf pos] prints the optional position [pos] on [ppf]. *)
let short : popt Lplib.Base.pp = fun ppf p ->
  match p with
  | None    -> string ppf "unknown location"
  | Some(p) -> let print_fname=false in
               string ppf (to_string ~print_fname p)

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

(** [make_pos lps elt] creates a located element from the lexing positions
   [lps] and the element [elt]. *)
let make_pos : Lexing.position * Lexing.position -> 'a -> 'a loc =
  fun lps elt -> in_pos (locate lps) elt

(** [deref sep dels pos] prints the text at the position, if possible.
    [sep] is the separator used between entries (e.g. "<br>\n")
    [dels] is a pair of delimiters used to wrap the "unknown location"
    message returned when the position does not refer to a file *)
let deref :
 separator:string -> delimiters:(string*string) -> popt Lplib.Base.pp =
 fun ~separator ~delimiters:(db,de) ppf pos ->
  match pos with
  | Some { fname=Some fname; start_line; start_col; end_line; end_col } ->
     let ch = open_in fname in
     let out = Buffer.create ((end_line - start_line) * 80 + end_col + 1) in
     for i = 0 to start_line - 2 do
      ignore (input_line ch)
     done ;
     for i = 0 to start_col - 1 do
      ignore (input_char ch)
     done ;
     for i = 0 to end_line - start_line - 1 do
       Buffer.add_string out (input_line ch) ;
       Buffer.add_string out separator
     done ;
     let end_col =
      if start_line = end_line then end_col - start_col else end_col in
     for i = 0 to end_col - 1 do
      Buffer.add_char out (input_char ch)
     done ;
     close_in ch ;
     string ppf (Buffer.contents out)
  | None | Some {fname=None} -> string ppf (db ^ "unknown location" ^ de)
