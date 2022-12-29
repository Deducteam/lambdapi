open Common
open Core
open Term
open Sig_state
open Parsing

(** Hack to parse easily a single term *)
let parse_term s =
  (* A hack to parse a term: wrap term [s] into [compute s;]. *)
  let c = "compute " ^ s ^ ";" in
  let command = Stream.next (Parser.Lp.parse_string "term" c) in
  match command.elt with
  | Syntax.P_query { elt = Syntax.P_query_normalize (t, _); _ } -> t
  | _ -> assert false

let scope_term ?(env = []) ss = Scope.scope_term true ss env

let add_sym (ss, slist) id =
  let ss, sym =
    Sig_state.add_symbol ss Public Defin Eager true (Pos.none id) Term.mk_Type
      [] None
  in
  (ss, sym :: slist)

let sig_state : Sig_state.t =
  let sign = Sig_state.create_sign (Path.ghost "cnfnnf") in
  Sig_state.of_sign sign

(** Builtin configuration for propositional logic. *)

let fol_symb_str = [ "P"; "t"; "∨"; "∧"; "⇒"; "⊥"; "⊤"; "¬"; "∃"; "∀" ]

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config slist =
  let get n = List.nth slist n in
  Handle.Fol.
    {
      symb_P = get 0;
      symb_T = get 1;
      symb_or = get 2;
      symb_and = get 3;
      symb_imp = get 4;
      symb_bot = get 5;
      symb_top = get 6;
      symb_not = get 7;
      symb_ex = get 8;
      symb_all = get 9;
    }

let mk_env symb_p =
  let tv = [ "A"; "B" ] in
  let rec aux e tlist =
    let tb_p = _Symb symb_p in
    match tlist with
    | hd :: tl -> aux (Env.add (new_tvar hd) tb_p None e) tl
    | [] -> e
  in
  aux Env.empty tv

(** Setup a signature state, a first order logic configuration and an
    environment to scope properly formulae. *)
let sig_state, cfg =
  let ss, symlist = List.fold_left add_sym (sig_state, []) fol_symb_str in
  Timed.(Print.sig_state := sig_state);
  (ss, get_config (List.rev symlist))

(** An environment defining two variables [A] and [B]. *)
let env = Env.empty
          |> Env.add (new_tvar "A") _Kind None
          |> Env.add (new_tvar "B") _Kind None

let test_nnf () =
  let formula =
    parse_term "∀ P (λ x1 : A, ¬ (∃ B (λ y1, ∨ (∨ x1 y1) ⊥)))"
    |> scope_term ~env sig_state
  in
  let witness = "∀ P (λ x1, ∀ B (λ y1, ∧ (∧ (¬ x1) (¬ y1)) ⊤))" in
  Alcotest.(check string)
    "Negation normal form" witness
    (Format.asprintf "%a" Print.term (Handle.Skolem.nnf cfg formula))

let test_pnf () =
  let formula =
    parse_term "∨ (∀ P (λ x1, x1)) A" |> scope_term ~env sig_state
  in
  let witness = "∀ P (λ x1, ∨ x1 A)" in
  Alcotest.(check string)
    "Prenex normal form" witness
    (Format.asprintf "%a" Print.term (Handle.Skolem.pnf cfg formula))

let _ =
  let open Alcotest in
  run "proposition transformations"
    [
      ( "prop",
        [ test_case "nnf" `Quick test_nnf; test_case "pnf" `Quick test_pnf ] );
    ]
