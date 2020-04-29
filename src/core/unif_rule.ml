(** Symbols and signature for unification rules.

    This module provides a signature to be used to handle unification rules.
    The signature is not attached to any real lambdapi file and is henceforth
    qualified to be a "ghost" signature. *)

open Timed
open Extra
open Files
open Terms

(** Path of the module. *)
let path = Path.ghost "unif_rule"

(** Ghost signature holding the symbols used in unification rules. This
    signature is an automatic dependency of all other signatures, and is
    automatically loaded. *)
let sign : Sign.t =
  let open Sign in
  let s =
    { sign_path = path; sign_symbols = ref StrMap.empty
    ; sign_deps = ref (PathMap.empty)
    ; sign_builtins = ref StrMap.empty; sign_unops = ref StrMap.empty
    ; sign_binops = ref StrMap.empty; sign_idents = ref StrSet.empty }
  in
  Sign.loaded := Files.PathMap.add path s !(Sign.loaded);
  s

(** Symbol representing an atomic unification problem. The term [equiv t
    u] represents [t ≡ u]. The left-hand side of a unification rule is
    made of only one unification. *)
let equiv : sym =
  Sign.add_symbol sign Public Defin (Pos.none "#equiv") Kind []

(** Cons-like symbol for equivalences. The right-hand side of a unification
    rule is made of a list of the form
    [comma (equiv t u) (comma (equiv v w) ...)] pretty-printed
    [t ≡ u, v ≡ w, ...]. *)
let comma : sym =
  Sign.add_symbol sign Public Defin (Pos.none "#comma") Kind []

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
