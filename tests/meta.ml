(** Test the Meta module. *)
open Common

open Handle
open Parsing
open Core

let term : Term.term Alcotest.testable =
  ( module struct
    type t = Term.term

    let pp = Print.pp_term
    let equal = Rewrite.eq
  end )

let scope_term ss t =
  Scope.scope_term true ss [] (Term.new_problem ()) (Fun.const None)
    (Fun.const None) t

let () = Library.set_lib_root (Some "/tmp")

(** The signature of [OK/bool.lp] *)
let bool_sig = Compile.Pure.compile_file "OK/bool.lp"

(** The signature state with [OK/bool.lp] opened. *)
let bool_sig_st =
  let open Core in
  let ss = Sig_state.of_sign bool_sig in
  Sig_state.open_sign ss bool_sig

(** The term [bool_or true true] *)
let or_true_true =
  Syntax.P.(appl_list (iden "bool_or") [ iden "true"; iden "true" ])
  |> scope_term bool_sig_st

(** Unit tests functions *)

let no_rewrite () =
  let no_rewrite = Tool.Meta.rewrite_with bool_sig [] or_true_true in
  Alcotest.(check term) "same term" or_true_true no_rewrite

let simple_rewrite () =
  let lhs = Syntax.P.iden "bool_or" in
  let rhs = Syntax.P.iden "bool_and" in
  let r =
    Scope.scope_rule bool_sig_st (Pos.none (lhs, rhs))
  in
  let r = (r.Pos.elt.pr_sym, Scope.rule_of_pre_rule r) in
  let rewritten =
    Tool.Meta.rewrite_with bool_sig [ r ] or_true_true
  in
  let and_true_true =
    Syntax.P.(appl_list (iden "bool_and") [ iden "true"; iden "true" ])
    |> scope_term bool_sig_st
  in
  Alcotest.(check term) "same term" and_true_true rewritten

(* Meta rewrite rules can rewrite symbols noted "constant". *)
let rewrite_constant () =
  let lhs = Syntax.P.iden "true" in (* [true] is constant *)
  let rhs = Syntax.P.iden "false" in
  let r =
    Scope.scope_meta_rule bool_sig_st (Pos.none (lhs, rhs))
  in
  let r = (r.Pos.elt.pr_sym, Scope.rule_of_pre_rule r) in
  let or_false_false =
    Syntax.P.(appl_list (iden "bool_or") [ iden "false"; iden "false" ])
    |> scope_term bool_sig_st
  in
  let rewritten = Tool.Meta.rewrite_with bool_sig [ r ] or_true_true in
  Alcotest.check term "same term" or_false_false rewritten

let () =
  let open Alcotest in
  run "Meta"
    [ ( "standard"
      , [ ("no rewriting with signature's rules", `Quick, no_rewrite)
        ; ("rewrite symbol", `Quick, simple_rewrite)
        ; ("rewrite constant", `Quick, rewrite_constant)
        ] )
    ]
