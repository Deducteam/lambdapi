#!/usr/bin/ocaml
#use "topfind"
#require "unix"
(* Benchmarks on libraries.  Should be called at the root of the
   repo. *)

open Unix

let libraries =
  [ "dklib"
  ; "focalide" ]

let prepare lib =
  putenv "LAMBDAPI" "/bin/true" ;
  chdir "libraries/" ;
  ignore @@ system ("./" ^ lib ^ ".sh") ;
  chdir "../"

let timelib ~repeat lib =
  chdir ("libraries/" ^ lib) ;
  let t = gettimeofday () in
  for i = 1 to repeat do
    ignore @@ system @@ "../../lambdapi " ^ lib ^ ".dk > /dev/null"
  done ;
  chdir "../.." ;
  (gettimeofday () -. t) /. (float_of_int repeat)

let () =
  List.iter prepare libraries ;
  let times = List.map (timelib ~repeat:10) libraries in
  List.iter2 (Printf.printf "%s: %fs\n")
    libraries times
