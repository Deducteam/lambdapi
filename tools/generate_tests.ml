#!/usr/bin/env ocaml

module F = Filename
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

(** [large_thump n] builds a tree of depth one but with many
    branches. *)
let thump n =
  let fname = F.concat testdir "thump.lp" in
  let ochan = open_out fname in
  P.fprintf ochan "%s\n" natural_prelude ;
  for i = 0 to n do
    P.fprintf ochan "symbol s%d : N\n" i
  done ;
  P.fprintf ochan "symbol thump : N ⇒ N\n" ;
  P.fprintf ochan "rule thump s0 → s0\n" ;
  for i = 0 to n do
    P.fprintf ochan "and thump s%d → 0\n" i
  done ;
  for i = 0 to n do
    P.fprintf ochan "assert thump s%d ≡ 0\n" i
  done ;
  close_out ochan

(** [comb n] creates a comb, that is an unbalanced tree with each node
    having a child on [s] and a rule on [z]. *)
let comb n =
  let fname = F.concat testdir "comb.lp" in
  let ochan = open_out fname in
  P.fprintf ochan "%s\n" natural_prelude ;
  P.fprintf ochan "symbol comb : N ⇒ N\n" ;
  P.fprintf ochan "rule comb 0 → 0\n" ;
  for i = 1 to n do
    P.fprintf ochan "and comb %d → z\n" i
  done ;
  P.fprintf ochan
  "symbol collect : N ⇒ N
rule collect (s &n) → (comb (s &n)) + (collect &n)
 and collect 0      → 0
assert collect %d ≡ %d
"  n 0;
  close_out ochan

let () =
  let usage = Printf.sprintf "Usage: %s [-c <int>] [-t <int>]" Sys.argv.(0) in
  Arg.parse speclist (fun _ -> Arg.usage speclist usage) usage ;
  thump !p_thump ;
  comb !p_comb
