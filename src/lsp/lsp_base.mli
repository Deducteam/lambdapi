(************************************************************************)
(* The λΠ-modulo Interactive Proof Assistant                            *)
(************************************************************************)

(************************************************************************)
(* λΠ-modulo serialization Toplevel                                     *)
(* Copyright 2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Common
open Handle

module J = Yojson.Basic

val std_protocol : bool ref

val mk_range : Pos.pos -> J.t

val mk_reply : id:int -> result:J.t -> J.t

val mk_diagnostics
  : uri:string
  -> version: int
  -> (Pos.pos * int * string * Goal.info list option) list
  -> J.t

val json_of_goals : ?logs:string -> Goal.info list option -> J.t
