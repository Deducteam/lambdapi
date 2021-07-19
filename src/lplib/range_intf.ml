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

(** Module for points and intervals. Used to determine if a cursor is in the
   range of a specific token, which is an interval of points (cursor
   positions). The presence of t and compare make [RangeType] an [OrderedType]
   (in the sense of [Map]). For now, the useful modules out of this library
   are [Range] and [RangeMap]. *)
module type S = sig
  type point
  type t

  (** [make_point ln col] creates a point with line [ln] and column [col]. *)
  val make_point : int -> int -> point

  (** [make_interval s e] creates an interval with start [s] and end [e].
      Requires the interval to be well defined (e.g with start < finish) or it
      will assert *)
  val make_interval : point -> point -> t

  val line : point -> int
  val column : point -> int
  val interval_start : t -> point
  val interval_end : t -> point

  (** Type for the position of a cursor relative to an interval. *)
  type cmp =
    | Before
    | In
    | After
        (** [in_range pt i] returns [Before], [In] or [After] depending on the
            position of the point [pt] relative to the interval [i].*)

  val in_range : point -> t -> cmp

  (** Comparison over intervals.

      An interval is considered "smaller" than another if its ending point is
      before the starting point of the other.

      Intervals need to be well defined (i.e returned by make_interval). Two
      intervals are considered equal if one is included in the other. In any
      other case, overlapping intervals can't be compared and will throw an
      error. *)
  val compare : t -> t -> int

  val point_to_string : point -> string
  val interval_to_string : t -> string

  (** [translate i ds df] returns the interval [i] with its starting point
      translated by [ds] and finishing point translated by [df].

      Will throw an error if the resulting interval is not well-defined (see
      make_interval). Only translates column-wise, does not modify the line
      coordinates of the extremity points. *)
  val translate : t -> int -> int -> t
end
