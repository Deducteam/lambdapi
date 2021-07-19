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

(* The functor for cursor maps. *)
module Make (Range : Range_intf.S) = struct
  (* A map of which keys are intervals. *)
  module Range = Range
  module RangeMap = Map.Make (Range)

  (* Now we need to transform the map so that : - the keys for "add" are
     intervals - the keys for "find" are points. *)
  type 'a t = (Range.t * 'a) RangeMap.t

  let point_to_interval pt = Range.make_interval pt pt

  let find cursor map =
    let interv = point_to_interval cursor in
    RangeMap.find_opt interv map

  let empty = RangeMap.empty
  let add interv elt map = RangeMap.add interv (interv, elt) map

  let to_string elt_to_string (map : 'a t) =
    let f key elt str =
      let _, e = elt in
      Range.interval_to_string key
      ^ "Token : " ^ elt_to_string e ^ "\n\n" ^ str
    in
    RangeMap.fold f map ""
end

(* The implementation of CursorMap using a functor. *)
include Make (Range)
