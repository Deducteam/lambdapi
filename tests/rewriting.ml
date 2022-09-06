open Common
open Pos
open Core
open Parsing

let parse_term s =
  (* A hack to parse a term: wrap term [s] into [compute s;]. *)
  let c = "compute " ^ s ^ ";" in
  let command = (Stream.next (Parser.Lp.parse_string "term" c)) in
  match command.elt with
  | Syntax.P_query {elt=Syntax.P_query_normalize (t, _); _} -> t
  | _ -> assert false

let scope_term ss = Scope.scope_term true ss []

let add_sym ss id =
  Sig_state.add_symbol ss Public Defin Eager true (Pos.none id) Term.mk_Kind []
    None

(* Define a signature state and some symbols. *)

let sig_state : Sig_state.t =
  let sign = Sig_state.create_sign (Path.ghost "rewriting_tests") in
  Sig_state.of_sign sign

let sig_state, c = add_sym sig_state "C"
let sig_state, ok = add_sym sig_state "Ok"
let sig_state, a = add_sym sig_state "A"

let parse_rule s =
  let r = Parser.Lp.parse_string "rewrite_test rule" s |> Stream.next in
  let r = match r.elt with Syntax.P_rules [r] -> r | _ -> assert false in
  Scope.scope_rule false sig_state r

let arrow_matching () =
  (* Matching on a product. *)
  let (c, _) as rule = parse_rule "rule C (A → A) ↪ Ok;" in
  Sign.add_rule sig_state.signature rule;
  Tree.update_dtree c [];
  let lhs = parse_term "C (A → A)" |> scope_term sig_state in
  Alcotest.(check bool)
    "C (A → A) matches C (A → A)"
    true
    (match Eval.snf [] lhs with Symb s -> s == ok | _ -> false)

(* Revert modifications performed on the signature. *)
let arrow_matching = Timed.pure_apply arrow_matching

let prod_matching () =
  let (c,_) as rule = parse_rule "rule C (Π _: _, A) ↪ Ok;" in
  Sign.add_rule sig_state.signature rule;
  Tree.update_dtree c [];
  let lhs = parse_term "C (A → A)" |> scope_term sig_state in
  Alcotest.(check bool)
    "C (A → A) matches C (Π _: _, A)"
    true
    (match Eval.snf [] lhs with Symb s -> s == ok | _ -> false)

let prod_matching = Timed.pure_apply prod_matching

let arrow_default () =
  (* Assert that a product can be considered as a default case. *)
  let (c,_) as rule = parse_rule "rule C _ ↪ Ok;" in
  Sign.add_rule sig_state.signature rule;
  Tree.update_dtree c [];
  let lhs = parse_term "C (A → A)" |> scope_term sig_state in
  Alcotest.(check bool)
    "C (A → A) matches C _"
    true
    (match Eval.snf [] lhs with Symb s -> s == ok | _ -> false)

(* Revert modifications performed on the signature. *)
let arrow_default = Timed.pure_apply arrow_default

let type_matching () =
  let rule = parse_rule "rule C TYPE ↪ Ok;" in
  Sign.add_rule sig_state.signature rule;
  Tree.update_dtree c [];
  let lhs = parse_term "C TYPE" |> scope_term sig_state in
  Alcotest.(check bool)
    "C TYPE matches C TYPE"
    true
    (match Eval.snf [] lhs with Symb s -> s == ok | _ -> false)

let type_matching = Timed.pure_apply type_matching

let type_default () =
  let rule = parse_rule "rule C _ ↪ Ok;" in
  Sign.add_rule sig_state.signature rule;
  Tree.update_dtree c [];
  let lhs = parse_term "C TYPE" |> scope_term sig_state in
  Alcotest.(check bool)
    "C TYPE matches C _"
    true
    (match Eval.snf [] lhs with Symb s -> s == ok | _ -> false)

let _ =
  let open Alcotest in
  run "rewrite engine" [
    ("matching", [ test_case "arrow" `Quick arrow_matching
                 ; test_case "prod" `Quick prod_matching
                 ; test_case "arrow default" `Quick arrow_default
                 ; test_case "TYPE" `Quick type_matching
                 ; test_case "TYPE default" `Quick type_default ] )
  ]
