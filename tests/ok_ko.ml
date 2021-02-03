(** Compile files in "OK" and "KO". *)
open Core

let compile = Handle.Compile.Pure.compile_file

let test_ok f () =
  (* Simply assert that there is no exception raised. *)
  Alcotest.(check unit) f (ignore (compile f)) ()

let test_ko f () =
  (* Succeed if compilation fails. *)
  let r = try (ignore (compile f)); true with _ -> false in
  Alcotest.(check bool) f r false

let _ =
  Files.set_lib_root None;
  let open Alcotest in
  let files = Sys.readdir "OK" |> Array.map (fun f -> "OK/" ^ f)
(* TODO put back OK/unif_hint.lp when it is fixed *)
  |> Array.to_list
  |> List.filter (function f -> f <> "OK/unif_hint.lp")
  |> Array.of_list in
  let tests_ok = Array.map (fun f -> test_case f `Quick (test_ok f)) files in
  let files = Sys.readdir "KO" |> Array.map (fun f -> "KO/" ^ f) in
  let tests_ko = Array.map (fun f -> test_case f `Quick (test_ko f)) files in
  run "Std"
    [ ("OK", Array.to_list tests_ok)
    ; ("KO", Array.to_list tests_ko) ]
