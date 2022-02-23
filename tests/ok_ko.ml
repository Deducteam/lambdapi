(** Compile files in "OK" and "KO". *)

let compile = Timed.pure_apply Handle.Compile.compile_file

let test_ok f () =
  (* Simply assert that there is no exception raised. *)
  Alcotest.(check unit) f (ignore (compile f)) ()

let test_ko f () =
  (* Succeed if compilation fails. *)
  let r = try ignore (compile f); true with _ -> false in
  Alcotest.(check bool) f r false

let _ =
  (* Set library root to avoid creating files out of the sandbox when
     opam runs tests. *)
  Common.Library.set_lib_root (Some (Sys.getcwd ()));
  let open Alcotest in
  let files = Lplib.Extra.files Common.Library.is_valid_src_extension "OK" in
  (* Remove files using a prover. *)
  let does_not_use_prover = function
    | "OK/why3.lp" | "OK/why3_quantifiers.lp" -> false
    | _ -> true
  in
  let files = List.filter does_not_use_prover files in
  let tests_ok = List.map (fun f -> test_case f `Quick (test_ok f)) files in
  let files = Lplib.Extra.files Common.Library.is_valid_src_extension "KO" in
  let tests_ko = List.map (fun f -> test_case f `Quick (test_ko f)) files in
  run "Std" [("OK", tests_ok); ("KO", tests_ko)]
