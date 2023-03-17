(** Test decision trees to graph export *)

open Common
open Handle
open Core

let () =
  Library.set_lib_root (Some "/tmp");
  Timed.(Console.verbose := 0);
  let sign = Compile.PureUpToSign.compile_file "../OK/boolean.lp" in
  let ss = Sig_state.of_sign sign in
  (* Regular symbol *)
  let sym =
    Sig_state.find_sym ~prt:true ~prv:true ss
      (Pos.none ([ "tests"; "OK"; "boolean" ], "bool_or"))
  in
  Format.printf "=> tests.OK.boolean.bool_or@\n";
  Tool.Tree_graphviz.to_dot Format.std_formatter sym;
  (* Ghost symbol *)
  (* We don't use [Pure] to keep rules added to unif hint symbols *)
  ignore @@ Compile.compile_file "../OK/unif_hint.lp";
  Format.printf "=> ghost symbol ≡ from tests.OK.unif_hint@\n";
  Tool.Tree_graphviz.to_dot Format.std_formatter Unif_rule.equiv
