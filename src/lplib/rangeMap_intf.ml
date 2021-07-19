(************************************************************************)
(* The λΠ-modulo Interactive Proof Assistant *)
(************************************************************************)

(************************************************************************)
(* λΠ-modulo serialization Toplevel *)
(* Copyright Inria -- Dual License LGPL 2.1 / GPL3+                     *)
(* Written by: F. Blanqui, E. J. Gallego Arias, F. Lefoulon             *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

module type S = sig
  (** Maps a position of the cursor (point) to the corresponding token of type
     'a in a given text editor with a .lp file open. *)
  type 'a t

  module Range : Range_intf.S

  (** The empty range map.*)
  val empty : 'a t

  (** [find pt map] returns the only (token, range) couple in map such that
     [pt] is a point within the mapped interval range. Requires [map] to be
     well-defined (see add). *)
  val find : Range.point -> 'a t -> (Range.t * 'a) option

  (** [add range token map] adds a mapping (key : [range], value : [token]) to
      [map].

      Requires all added keys to be non overlapping intervals to be
      well-defined. /!\ Does not ensure proper functionning if the added keys
      are overlapping intervals, e.g might change a previously added (key,
      element) couple or throw an error. *)
  val add : Range.t -> 'a -> 'a t -> 'a t

  val to_string : ('a -> string) -> 'a t -> string
end
