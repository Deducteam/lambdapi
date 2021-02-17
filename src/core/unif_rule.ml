(** Symbols and signature for unification rules.

    This module provides a signature to be used to handle unification rules.
    The signature is not attached to any real lambdapi file and is henceforth
    qualified to be a "ghost" signature. *)

open Common
open Timed
open Term
open Parsing.LpLexer

(** Ghost signature holding the symbols used in unification rules.
    - All signatures depend on it (dependency set in
      {!val:Sig_state.create_sign}).
    - All signatures open it (opened in {!val:Sig_state.of_sign}).
    - It is automatically loaded. *)
let sign : Sign.t =
  let dummy = Sign.dummy () in
  let s = {dummy with Sign.sign_path = unif_rule_path} in
  Sign.loaded := Path.Map.add unif_rule_path s !(Sign.loaded);
  s

(** Symbol representing an atomic unification problem. The term [equiv t
    u] represents [t ≡ u]. The left-hand side of a unification rule is
    made of only one equation. *)
let equiv : sym =
  let sym =
    Sign.add_symbol sign Public Defin Eager false (Pos.none "equiv") Kind []
  in
  let qid = Pos.none (unif_rule_path, equiv) in
  let binop = ("≡", Pratter.Neither, 1.1, qid) in
  Sign.add_binop sign sym binop;
  sym

(** Cons-like symbol for equivalences. The right-hand side of a unification
    rule is made of a list of the form
    [cons (equiv t u) (cons (equiv v w) ...)] pretty-printed
    [t ≡ u; v ≡ w; ...]. *)
let cons : sym =
  let sym =
    Sign.add_symbol sign Public Const Eager true (Pos.none "cons") Kind []
  in
  let qid = Pos.none (unif_rule_path, cons) in
  let binop = (";", Pratter.Right, 1.0, qid) in
  Sign.add_binop sign sym binop;
  sym

(** [unpack eqs] transforms a term of the form
    [cons (equiv t u) (cons (equiv v w) ...)]
    into a list [[(t,u); (v,w); ...]]. *)
let rec unpack : term -> (term * term) list = fun eqs ->
  match LibTerm.get_args eqs with
  | (Symb(s), [v; w]) ->
      if s == cons then
        match LibTerm.get_args v with
        | (Symb(e), [t; u]) when e == equiv -> (t, u) :: unpack w
        | _          (* Ill-formed term. *) -> assert false
      else if s == equiv then [(v, w)] else
      assert false (* Ill-formed term. *)
  | _                 -> assert false (* Ill-formed term. *)

(** [is_ghost s] is true iff [s] is a symbol of the ghost signature. *)
let is_ghost : sym -> bool = fun s -> s == equiv || s == cons
