(** Symbols and signature for unification rules.

    This module provides a signature to be used to handle unification rules.
    The signature is not attached to any real lambdapi file and is henceforth
    qualified to be a "ghost" signature. *)

open Common
open Timed
open Term
open Parsing

(** Ghost signature holding the symbols used in unification rules.
    - All signatures depend on it (dependency set in
      {!val:Sig_state.create_sign}).
    - All signatures open it (opened in {!val:Sig_state.of_sign}).
    - It is automatically loaded. *)
let sign : Sign.t =
  let dummy = Sign.dummy () in
  let sign = {dummy with Sign.sign_path = LpLexer.unif_rule_path} in
  Sign.loaded := Path.Map.add LpLexer.unif_rule_path sign !(Sign.loaded);
  sign

(** Symbol of name LpLexer.equiv, with infix notation. *)
let equiv : sym =
  let id = Pos.none LpLexer.equiv in
  let s = Sign.add_symbol sign Public Defin Eager false id Kind [] in
  Sign.add_notation sign s (Infix(Pratter.Neither, 1.1)); s

(** Symbol of name LpLexer.cons, with infix right notation with priority <
   LpLexer.equiv. *)
let cons : sym =
  let id = Pos.none LpLexer.cons in
  let s = Sign.add_symbol sign Public Const Eager true id Kind [] in
  Sign.add_notation sign s (Infix(Pratter.Right, 1.0)); s

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
