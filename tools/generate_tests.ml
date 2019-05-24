#!/usr/bin/env ocaml
#use "topfind"
#require "unix"

open Unix
module P = Printf

let testdir = "../tests/OK/"

let natural_prelude = "require open tests.OK.nat"

let rec triangle n = if n = 0 then 0 else triangle (n - 1) + n

(** [large_thump n] builds a tree of depth one but with many
    branches. *)
let large_thump n =
  let ochan = open_out (testdir ^ "large_thump.lp") in
  for i = 1 to n do
    P.fprintf ochan "symbol s%d : N\n" i
  done ;
  P.fprintf ochan "symbol f : N ⇒ N" ;
  P.fprintf ochan "rule f 0 → 0\n" ;
  for i = 1 to n do
    P.fprintf ochan "and f s%d → %d\n" i i
  done ;
  P.fprintf ochan
    "symbol sof : N ⇒ N
     rule sof (s &n) → (f (s &n)) + (sof &n)
     assert sof %d ≡ %d" n (triangle n) ;
  close_out ochan

let () =
  large_thump 1000
