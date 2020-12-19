(** Compile files in "OK" and "KO". *)
open Core

let compile = Compile.Pure.compile_file

let test_ok f () =
  (* Simply assert that there is no exception raised. *)
  Alcotest.(check unit) f (ignore (compile f)) ()

let test_ko f () =
  (* Succeed if compilation fails. *)
  let r = try (ignore (compile f)); true with _ -> false in
  Alcotest.(check bool) f r false

let test_one_folder : string -> string -> 'a array = fun main_folder specific_folder ->
  let current_folder = main_folder ^ "/" ^ specific_folder in
  let files =
    Sys.readdir current_folder |> Array.map (fun f -> current_folder ^ "/" ^ f)
    |> Array.to_list
    |> List.filter (function f -> f <> current_folder ^ "/" ^ "description")
    (* TODO put back OK/unif_hint.lp when it is fixed *)
    |> List.filter (function f -> f <> "OK/set_option/unif_hint.lp")
    |> Array.of_list
  in
  let test_fct = if main_folder = "OK" then test_ok else test_ko in
  Array.map (fun f -> Alcotest.test_case f `Quick (test_fct f)) files
  
let _ =
  Files.set_lib_root None;
  
  let test_parsing = test_one_folder "OK" "parsing" in
  let test_scoping = test_one_folder "OK" "scoping" in
  let test_import  = test_one_folder "OK" "import" in 
  let test_set_option = test_one_folder "OK" "set_option" in
  let test_queries = test_one_folder "OK" "queries" in
  let test_symbol = test_one_folder "OK" "symbol" in
  let test_rewriting = test_one_folder "OK" "rewriting" in
  let test_tactic = test_one_folder "OK" "tactic" in
  let test_examples = test_one_folder "OK" "examples" in
  Alcotest.run "Std"
    [ ("OK_parsing", Array.to_list test_parsing)
    ; ("OK_scoping", Array.to_list test_scoping)
    ; ("OK_import", Array.to_list test_import)
    ; ("OK_set_option", Array.to_list test_set_option)
    ; ("OK_queries", Array.to_list test_queries)
    ; ("OK_symbol", Array.to_list test_symbol)
    ; ("OK_rewriting", Array.to_list test_rewriting)
    ; ("OK_tactic", Array.to_list test_tactic) 
    ; ("OK_examples", Array.to_list test_examples) ]    

  (*                 
  
  let files = Sys.readdir "OK" |> Array.map (fun f -> "OK/" ^ f)
(* TODO put back OK/unif_hint.lp when it is fixed *)
  |> Array.to_list
  |> List.filter (function f -> f <> "OK/unif_hint.lp" && f <> "OK/theory")
  |> List.filter (function f -> not (Sys.is_directory f))
  |> Array.of_list in
  let tests_ok = Array.map (fun f -> test_case f `Quick (test_ok f)) files in
  let files = Sys.readdir "KO" |> Array.map (fun f -> "KO/" ^ f) in
  let tests_ko = Array.map (fun f -> test_case f `Quick (test_ko f)) files in
  run "Std"
    [ ("OK", Array.to_list tests_ok)
    ; ("KO", Array.to_list tests_ko) ]
   *)
