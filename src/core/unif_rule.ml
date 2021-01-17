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

(** Ghost signature holding the symbols used in unification rules.
    - All signatures depend on it (dependency set in
      {!val:Sig_state.create_sign}).
    - All signatures open it (opened in {!val:Sig_state.of_sign}).
    - It is automatically loaded. *)
let sign : Sign.t =
  let dummy = Sign.dummy () in
  let s = {dummy with Sign.sign_path = path} in
  Sign.loaded := Files.PathMap.add path s !(Sign.loaded);
  s

(** Symbol representing an atomic unification problem. The term [equiv t
    u] represents [t ≡ u]. The left-hand side of a unification rule is
    made of only one unification. *)
let equiv : sym =
  let path = List.map (fun s -> (s, false)) path in
  let bo = ("≡", Pratter.Neither, 1.1, Pos.none (path, "#equiv")) in
  let sym =
    Sign.add_symbol sign Public Defin Eager (Pos.none "#equiv") Kind []
  in
  Sign.add_binop sign "≡" (sym, bo);
  sym

(** Cons-like symbol for equivalences. The right-hand side of a unification
    rule is made of a list of the form
    [cons (equiv t u) (cons (equiv v w) ...)] pretty-printed
    [t ≡ u; v ≡ w; ...]. *)
let cons : sym =
  let path = List.map (fun s -> (s, false)) path in
  let bo = (";", Pratter.Right, 1.0, Pos.none (path, "#cons")) in
  let sym =
    Sign.add_symbol sign Public Defin Eager (Pos.none "#cons") Kind []
  in
  Sign.add_binop sign ";" (sym, bo);
  sym

(** [unpack eqs] transforms a term of the form
    [cons (equiv t u) (cons (equiv v w) ...)]
    into a list [[(t,u); (v,w); ...]]. *)
let rec unpack : term -> (term * term) list = fun eqs ->
  match Basics.get_args eqs with
  | (Symb(s), [v; w]) ->
      if s == cons then
        match Basics.get_args v with
        | (Symb(e), [t; u]) when e == equiv -> (t, u) :: unpack w
        | _          (* Ill-formed term. *) -> assert false
      else if s == equiv then [(v, w)] else
      assert false (* Ill-formed term. *)
  | _                 -> assert false (* Ill-formed term. *)

(** [p_unpack eqs] is [unpack eqs] on syntax-level equivalences [eqs]. *)
let rec p_unpack : p_term -> (p_term * p_term) list = fun eqs ->
  let id s = snd s.Pos.elt in
  match Syntax.p_get_args eqs with
  | ({elt=P_Iden(s, _); _}, [v; w]) ->
      if id s = "#cons" then
        match Syntax.p_get_args v with
        | ({elt=P_Iden(e, _); _}, [t; u]) when id e = "#equiv" ->
            (t, u) :: p_unpack w
        | _                                                         ->
            assert false (* Ill-formed term. *)
      else if id s = "#equiv" then [(v, w)] else
      assert false (* Ill-formed term. *)
  | _                               -> assert false (* Ill-formed term. *)

(** [is_ghost s] is true iff [s] is a symbol of the ghost signature. *)
let is_ghost : sym -> bool = fun s -> s == equiv || s == cons
