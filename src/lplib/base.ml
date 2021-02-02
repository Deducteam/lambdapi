(** Standard library extension (mostly). *)

(** Type of pretty-printing functions. *)
type 'a pp = Format.formatter -> 'a -> unit

let pp_sep : string -> unit pp = fun s ff () -> Format.pp_print_string ff s

(** Type of equality functions. *)
type 'a eq = 'a -> 'a -> bool

(** Type of comparison functions. *)
type 'a cmp = 'a -> 'a -> int

module Int = struct
  type t = int
  let compare = ( - )
end
