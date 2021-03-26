(** Compile files in "OK" and "KO". *)

let compile = Handle.Compile.Pure.compile_file

let test_ok f () =
  (* Simply assert that there is no exception raised. *)
  Alcotest.(check unit) f (ignore (compile f)) ()

let test_ko f () =
  (* Succeed if compilation fails. *)
  let r = try ignore (compile f); true with _ -> false in
  Alcotest.(check bool) f r false

let _ =
  Common.Library.set_lib_root None;
  let open Alcotest in
  let files = Lplib.Extra.files Common.Library.is_valid_src_extension "OK" in
  let tests_ok = List.map (fun f -> test_case f `Quick (test_ok f)) files in
  let files = Lplib.Extra.files Common.Library.is_valid_src_extension "KO" in
  let tests_ko = List.map (fun f -> test_case f `Quick (test_ko f)) files in
  run "Std" [("OK", tests_ok); ("KO", tests_ko)]
