(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = Format.formatter -> 'a -> unit

(** Pretty printable values. *)
module type PP = sig
  type t
  val pp : t pp
  (** [pp oc e] prints element [e] to formatter [oc]. *)
end

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

(** Values with an equality relation. *)
module type EQ = sig
  type t
  val eq : t eq
  (** [eq x y] is true if [x] and [y] are equal. *)
  end

(** Short name for the type of a comparison function. *)
type 'a cmp = 'a -> 'a -> int

module Int = struct
  type t = int

  let compare = ( - )
end
