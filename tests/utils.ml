(** Testing miscellanous utilities provided by Lambdapi, such as decision tree
    printing, XTC file generation, HRS file generation. *)

open Common
open Core
open Handle

let _ =
  Library.set_lib_root None;
  match Package.find_config "." with
  | None -> assert false
  | Some(f) -> Package.apply_config f

let compile (fname: string): Sign.t =
  Compile.compile false (Library.path_of_file Parsing.LpLexer.escape fname)

let bool_file = "OK/bool.lp"
let bool_sign = compile bool_file
let bool_ss = Sig_state.of_sign bool_sign

(** HRS file generation. *)
let test_hrs () =
  let buf = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer buf in
  Tool.Hrs.to_HRS fmt bool_sign;
  (* TODO: make more precise test (equality between results for instance). *)
  Alcotest.(check bool) "bool as HRS not empty" (Buffer.contents buf <> "") true

(** XTC file generation. *)
let test_xtc () =
  let buf = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer buf in
  Tool.Xtc.to_XTC fmt bool_sign;
  Alcotest.(check bool) "bool as XTC not empty" (Buffer.contents buf <> "") true

(** Decision tree of regular symbol. *)
let test_dtree () =
  let id = Pos.none (["tests";"OK";"bool"],"bool_or") in
  let sym = Sig_state.find_sym ~prt:true ~prv:true bool_ss id in
  let buf = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer buf in
  Tool.Tree_graphviz.to_dot fmt sym;
  Alcotest.(check bool) "bool" (Buffer.contents buf <> "") true

(** Decision tree of ghost symbols. *)
let test_dtree_ghost () =
  let file = "OK/unif_hint.lp" in
  ignore (compile file);
  let buf = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer buf in
  Tool.Tree_graphviz.to_dot fmt Unif_rule.equiv;
  Alcotest.(check bool) "bool" (Buffer.contents buf <> "") true

let _ =
  let open Alcotest in
  run "Utils"
    [ "hrs", [test_case "bool" `Quick test_hrs]
    ; "xtc", [test_case "bool" `Quick test_xtc]
    ; "dtree", [test_case "bool" `Quick test_dtree]
                 (*; "dtree_ghost", [test_case "bool" `Quick test_dtree_ghost]*)
    ]
