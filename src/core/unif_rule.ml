(** Symbols and signature for unification rules.

    This module provides a signature to be used to handle unification rules.
    The signature is not attached to any real lambdapi file and is henceforth
    qualified to be a "ghost" signature. *)

open Timed
open Files
open Terms
open Syntax

(** Path of the module. *)
let path = Path.ghost "unif_rule"

(** Ghost signature holding the symbols used in unification rules. This
    signature is an automatic dependency of all other signatures, is
    automatically loaded and automatically opened. *)
let sign : Sign.t =
  let s = {Sign.dummy with Sign.sign_path = path} in
  Sign.loaded := Files.PathMap.add path s !(Sign.loaded);
  s

(** Symbol representing an atomic unification problem. The term [equiv t
    u] represents [t ≡ u]. The left-hand side of a unification rule is
    made of only one unification. *)
let equiv : sym =
  let path = List.map (fun s -> (s, false)) path in
  let bo = ("≡", Assoc_none, 1.1, Pos.none (path, "#equiv")) in
  let sym = Sign.add_symbol sign Public Defin (Pos.none "#equiv") Kind [] in
  Sign.add_binop sign "≡" (sym, bo);
  sym

(** Cons-like symbol for equivalences. The right-hand side of a unification
    rule is made of a list of the form
    [comma (equiv t u) (comma (equiv v w) ...)] pretty-printed
    [t ≡ u, v ≡ w, ...]. *)
let comma : sym =
  let path = List.map (fun s -> (s, false)) path in
  let bo = (",", Assoc_right, 1.0, Pos.none (path, "#comma")) in
  let sym = Sign.add_symbol sign Public Defin (Pos.none "#comma") Kind [] in
  Sign.add_binop sign "," (sym, bo);
  sym

(** [unpack eqs] transforms a term of the form [t =? u, v =? w, ...]
    into a list [[t =? u; v =? w; ...]]. *)
let rec unpack : term -> (term * term) list = fun eqs ->
  match Basics.get_args eqs with
  | (Symb(s), [v; w]) ->
      if s == comma then
        match Basics.get_args v with
        | (Symb(e), [t; u]) when e == equiv -> (t, u) :: unpack w
        | _          (* Ill-formed term. *) -> assert false
      else if s == equiv then [(v, w)] else
      assert false (* Ill-formed term. *)
  | _                 -> assert false (* Ill-formed term. *)
