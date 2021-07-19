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

(* We follow LSP denominations except for end_ being reserved in OCaml. *)

type point = { line : int; character : int }
type t = { start : point; end_ : point }

let make_point line character = { line; character }

let make_interval start end_ =
  (* Fixme: don't rely on the lexicographic order *)
  assert (start <= end_);
  { start; end_ }

let line pt = pt.line
let column pt = pt.character
let interval_start i = i.start
let interval_end i = i.end_

type cmp = Before | In | After

let in_range pos { start; end_ } =
  (* Comparison operators work as lexicographic comparison on points (meaning
     l is compared, then c is compared). *)
  if pos < start then Before else if pos > end_ then After else In

let compare { start = s1; end_ = f1 } { start = s2; end_ = f2 } =
  if (s1 >= s2 && f1 <= f2) || (s1 <= s2 && f1 >= f2) then 0
  else if f1 <= s2 then -1
  else if s1 >= f2 then 1
  else failwith "Intervals overlap, no inclusion between the two"

let point_to_string pt =
  "Line : " ^ string_of_int pt.line
  ^ "; Column : " ^ string_of_int pt.character ^ "\n"

let interval_to_string { start; end_ } =
  "From :\n" ^ point_to_string start ^ "To :\n" ^ point_to_string end_

let translate { start; end_ } ds df =
  let s2 = make_point (line start) (column start - ds) in
  let f2 = make_point (line end_) (column end_ + df) in
  assert (s2 <= f2);
  make_interval s2 f2
