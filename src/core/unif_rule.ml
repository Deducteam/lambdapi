(** Symbols and signature for unification rules.

    This module provides a signature to be used to handle unification rules.
    The signature is not attached to any real lambdapi file and is henceforth
    qualified to be a "ghost" signature. *)

open Common
open Term

(** Symbol of name LpLexer.equiv, with infix notation. *)
let equiv : sym =
  let id = Pos.none "≡" in
  let s = Sign.add_symbol Ghost.sign Public Defin Eager `None id mk_Kind [] in
  Sign.add_notation Ghost.sign s (Infix(Pratter.Neither, 1.1)); s

(** Symbol of name LpLexer.cons, with infix right notation with priority <
   LpLexer.equiv. *)
let cons : sym =
  let id = Pos.none ";" in
  let s = Sign.add_symbol Ghost.sign Public Const Eager `None id mk_Kind [] in
  Sign.add_notation Ghost.sign s (Infix(Pratter.Right, 1.0)); s

(** [unpack eqs] transforms a term of the form
    [cons (equiv t u) (cons (equiv v w) ...)]
    into a list [[(t,u); (v,w); ...]]. *)
let rec unpack : term -> (term * term) list = fun eqs ->
  match get_args eqs with
  | (Symb(s), [v; w]) ->
      if s == cons then
        match get_args v with
        | (Symb(e), [t; u]) when e == equiv -> (t, u) :: unpack w
        | _ -> assert false
      else if s == equiv then [(v, w)]
      else assert false
  | _ -> assert false
