(** Compile files in "OK" and "KO". *)
open Core

let test_ok f () =
  (* Simply assert that there is no exception raised. *)
  Alcotest.(check unit) f (ignore (Compile.compile_file f)) ()

let test_ko f () =
  (* Succeed if compilation fails. *)
  let r = try (ignore (Compile.compile_file f)); true with _ -> false in
  Alcotest.(check bool) f r false

let _ =
  Files.set_lib_root None;
  let open Alcotest in
  let files = Sys.readdir "OK" |> Array.map (fun f -> "OK/" ^ f) in
  let tests_ok = Array.map (fun f -> test_case f `Quick (test_ok f)) files in
  let files = Sys.readdir "KO" |> Array.map (fun f -> "KO/" ^ f) in
  let tests_ko = Array.map (fun f -> test_case f `Quick (test_ko f)) files in
  run "Std"
    [ ("OK", Array.to_list tests_ok)
    ; ("KO", Array.to_list tests_ko) ]
