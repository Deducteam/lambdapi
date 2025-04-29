(** Symbols and signature for unification rules.

    This module provides a signature to be used to handle unification rules.
    The signature is not attached to any real lambdapi file and is henceforth
    qualified to be a "ghost" signature. *)

open Common
open Term

(** Symbol "≡". *)
let equiv : sym =
  let id = Pos.none "≡" in
  let s =
    Sign.add_symbol Ghost.sign Public Defin Eager false id None Kind [] in
  Timed.(s.sym_not := Infix(Pratter.Neither, 2.0));
  s

(** Symbol ";". *)
let cons : sym =
  let id = Pos.none ";" in
  let s =
    Sign.add_symbol Ghost.sign Public Const Eager true id None Kind [] in
  Timed.(s.sym_not := Infix(Pratter.Right, 1.0));
  s

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

(** [mem s] is true iff [s] belongs to [sign]. *)
let mem : sym -> bool = fun s -> s == equiv || s == cons
