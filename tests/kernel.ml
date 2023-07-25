open Common
open Core

let () =
  (* Set library root to avoid creating files out of the sandbox when opam runs
     tests. *)
  Library.set_lib_root (Some (Sys.getcwd ()))

let open_sign_default () =
  (* Check that by default, [Sig_state.of_sign s] opens [s] *)
  let sign = Sig_state.create_sign [ "dummy" ] in
  let _ =
    Sign.add_symbol sign Term.Public Term.Defin Term.Eager false
      (Pos.none "foo") (Pos.none "") Term.mk_Type []
  in
  let ss = Sig_state.of_sign sign in
  Alcotest.(check unit)
    "find_sym succeeds"
    (ignore @@ Sig_state.find_sym ~prt:true ~prv:true ss (Pos.none ([], "foo")))
    ()

let () =
  let open Alcotest in
  run "Kernel"
    [ ( "Signatures management"
      , [ test_case "Signature opened in sig state" `Quick open_sign_default ]
      )
    ]
