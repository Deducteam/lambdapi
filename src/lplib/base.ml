(** Standard library extension (mostly). *)

(** Type of pretty-printing functions. *)
type 'a pp = Format.formatter -> 'a -> unit

let pp_sep : string -> unit pp = fun s ff () -> Format.pp_print_string ff s

(** Type of equality functions. *)
type 'a eq = 'a -> 'a -> bool

(** Type of comparison functions. *)
type 'a cmp = 'a -> 'a -> int

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a,'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

module Int = struct
  type t = int
  let compare = ( - )
end
