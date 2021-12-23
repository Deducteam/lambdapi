open Common
open Core

let () =
  (* Set library root to avoid creating files out of the sandbox when opam runs
     tests. *)
  Library.set_lib_root (Some (Sys.getcwd ()))

let not_opened_sign () =
  let sign = Sig_state.create_sign [ "dummy" ] in
  let _ =
    Sign.add_symbol sign Term.Public Term.Defin Term.Eager false
      (Pos.none "foo") Term.mk_Type []
  in
  let ss = Sig_state.of_sign sign in
  Alcotest.(check unit)
    "find_sym fails"
    ( try
        ignore
        @@ Sig_state.find_sym ~prt:true ~prv:true ss (Pos.none ([], "foo"))
      with Error.Fatal (_, _) -> () )
    ()

let open_sign () =
  let sign = Sig_state.create_sign [ "dummy" ] in
  let _ =
    Sign.add_symbol sign Term.Public Term.Defin Term.Eager false
      (Pos.none "foo") Term.mk_Type []
  in
  let ss = Sig_state.of_sign sign in
  let ss = Sig_state.open_sign ss sign in
  Alcotest.(check unit)
    "find_sym succeeds"
    (ignore @@ Sig_state.find_sym ~prt:true ~prv:true ss (Pos.none ([], "foo")))
    ()

let () =
  let open Alcotest in
  run "Kernel"
    [ ( "Signatures management"
      , [ test_case "Signature not opened upon signature state creation" `Quick
            not_opened_sign
        ; test_case "Opening signature in signature state" `Quick open_sign
        ] )
    ]
