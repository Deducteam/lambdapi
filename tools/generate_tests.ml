#!/usr/bin/env ocaml
#use "topfind"
#require "unix"

open Unix
module P = Printf

let p_thump = ref 20
let p_comb = ref 20

let speclist = Arg.align
  [ ( "-t"
    , Arg.Int ((:=) p_thump)
    , " Width of thump." )
  ; ( "-c"
    , Arg.Int ((:=) p_comb)
    , " Depth of comb.")
  ]

let testdir = "../tests/OK/"

let natural_prelude = "require open tests.OK.nat"

let rec triangle n = if n = 0 then 0 else n + (triangle (n - 1))

(** [large_thump n] builds a tree of depth one but with many
    branches. *)
let thump n =
  let ochan = open_out (testdir ^ "large_thump.lp") in
  P.fprintf ochan "%s\n" natural_prelude ;
  for i = 0 to n do
    P.fprintf ochan "symbol s%d : N\n" i
  done ;
  P.fprintf ochan "symbol f : N ⇒ N\n" ;
  P.fprintf ochan "rule f s0 → s0\n" ;
  for i = 1 to n do
    P.fprintf ochan "and f s%d → 0\n" i
  done ;
  for i = 1 to n do
    P.fprintf ochan "assert f s%d ≡ 0\n" i
  done ;
  close_out ochan

(** [comb n] creates a comb, that is a unbalanced tree with each node
    having a child on [s] and a rule on [z]. *)
let comb n =
  let ochan = open_out (testdir ^ "comb.lp") in
  P.fprintf ochan "%s\n" natural_prelude ;
  P.fprintf ochan "symbol comb : N ⇒ N\n" ;
  P.fprintf ochan "rule comb 0 → 0\n" ;
  for i = 1 to n do
    P.fprintf ochan "and comb %d → %d\n" i i
  done ;
  P.fprintf ochan
  "symbol sof : N ⇒ N
rule sof (s &n) → (comb (s &n)) + (sof &n)
 and sof 0      → 0
assert sof %d ≡ %d
" n (triangle n) ;
  close_out ochan

let () =
  let usage = Printf.sprintf "Usage: %s [-c <int>] [-t <int>]" Sys.argv.(0) in
  Arg.parse speclist (fun _ -> Arg.usage speclist usage) usage ;
  thump !p_thump ;
  comb !p_comb
