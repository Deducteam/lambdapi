(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = Format.formatter -> 'a -> unit

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

(** Short name for the type of a comparison function. *)
type 'a cmp = 'a -> 'a -> int

module Int = struct
  type t = int

  let compare = ( - )
end
