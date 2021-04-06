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

let rule_of_pre_rule : Scope.pre_rule -> Term.rule =
  fun {pr_lhs; pr_vars; pr_rhs; pr_arities; pr_xvars_nb; _} ->
  { lhs = pr_lhs
  ; rhs = Bindlib.(unbox (bind_mvar pr_vars pr_rhs))
  ; arity = List.length pr_lhs
  ; arities = pr_arities
  ; vars = pr_vars
  ; xvars_nb = pr_xvars_nb }

let add_sym ss id =
  Sig_state.add_symbol ss Public Defin Eager true (Pos.none id) Kind [] None

(* Define a signature state and some symbols. *)

let sig_state : Sig_state.t =
  let sign = Sig_state.create_sign (Sign.ghost_path "rewriting_tests") in
  Sig_state.of_sign sign

let sig_state, c = add_sym sig_state "C"
let sig_state, ok = add_sym sig_state "Ok"
let sig_state, a = add_sym sig_state "A"

let parse_rule s =
  let r = Parser.Lp.parse_string "rewrite_test rule" s |> Stream.next in
  let r = match r.elt with Syntax.P_rules [r] -> r | _ -> assert false in
  (Scope.scope_rule false sig_state r).elt |> rule_of_pre_rule

let prod_matching () =
  (* Matching on a product. *)
  let rule = parse_rule "rule C (A → A) ↪ Ok;" in
  Sign.add_rule sig_state.signature c rule;
  Tree.update_dtree c;
  let lhs = parse_term "C (A → A)" in
  let lhs =
    Scope.scope_term true sig_state [] (lazy Lplib.Extra.IntMap.empty) lhs
  in
  Alcotest.(check bool)
    "ok"
    (match Eval.snf [] lhs with Symb s -> s == ok | _ -> false)
    true

(* Revert modifications performed on the signature. *)
let prod_matching = Timed.pure_apply prod_matching

let prod_default () =
  (* Assert that a product can be considered as a default case. *)
  let rule = parse_rule "rule C _ ↪ Ok;" in
  Sign.add_rule sig_state.signature  c rule;
  Tree.update_dtree c;
  let lhs = parse_term "C (A → A)" in
  let lhs =
    Scope.scope_term true sig_state [] (lazy Lplib.Extra.IntMap.empty) lhs
  in
  Alcotest.(check bool)
    "Ok"
    (match Eval.snf [] lhs with Symb s -> s == ok | _ -> false)
    true

(* Revert modifications performed on the signature. *)
let prod_default = Timed.pure_apply prod_default

let _ =
  let open Alcotest in
  run "rewrite engine" [
    ("matching", [ test_case "product" `Quick prod_matching
                 ; test_case "default" `Quick prod_default ] )
  ]
