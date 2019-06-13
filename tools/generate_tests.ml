#!/usr/bin/env ocaml
(** Generates tests files in [../tests/OK/].  Tests mainly concern
    performance of rule filetering. *)

module F = Filename
module P = Printf

let p_thump = ref 20
let p_comb = ref 20

let outdir = ref "../tests/OK"

let speclist = Arg.align
  [ ( "-t"
    , Arg.Set_int p_thump
    , " Width of thump." )
  ; ( "-c"
    , Arg.Set_int p_comb
    , " Depth of comb.")
  ; ( "--outdir"
    , Arg.Set_string outdir
    , "Output directory, ../tests/OK by default." )
  ]


let natural_prelude = "require open tests.OK.nat"

(** [thump n] builds a tree of depth one with [n] branches. *)
let thump n =
  let fname = F.concat !outdir "thump.lp" in
  let ochan = open_out fname in
  P.fprintf ochan "%s\n" natural_prelude ;
  for i = 0 to n do
    P.fprintf ochan "symbol s%d : N\n" i
  done ;
  P.fprintf ochan "symbol thump : N ⇒ N
rule thump s0 → 0\n" ;
  for i = 1 to n do
    P.fprintf ochan "and thump s%d → 0\n" i
  done ;
  P.fprintf ochan "symbol loop : N ⇒ N ⇒ N
rule loop (s &x) 0 → loop &x (thump s%d)
assert loop 60000 (thump s%d) ≡ loop 0 0" n n ;
  close_out ochan

(** [comb n] creates a comb, that is an unbalanced tree with each node
    having a child on [s] and a rule on [z]. *)
let comb n =
  let fname = F.concat !outdir "comb.lp" in
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
  Arg.parse speclist (fun _ -> raise @@ Arg.Bad "no anon args") usage ;
  thump !p_thump ;
  comb !p_comb
