(** Parser level terms. *)

open Lplib
open Lplib.Base
open Pos
open Syntax

(** Parser-level (located) term representation. *)
type p_term = p_term_aux loc
and p_term_aux =
  | P_Type
  (** TYPE constant. *)
  | P_Iden of qident * bool
  (** Identifier (the boolean indicates whether it is prefixed by "@"). *)
  | P_Wild
  (** Wildcard (place-holder for terms). *)
  | P_Meta of strloc * p_term array option
  (** Meta-variable with the given environment. *)
  | P_Patt of strloc option * p_term array option
  (** Named or unnamed higher-order pattern (used for rules LHS / RHS). *)
  | P_Appl of p_term * p_term
  (** Application. *)
  | P_Impl of p_term * p_term
  (** Implication. *)
  | P_Abst of p_term p_arg list * p_term
  (** Abstraction over several variables. *)
  | P_Prod of p_term p_arg list * p_term
  (** Product over several variables. *)
  | P_LLet of ident * p_term p_arg list * p_type option * p_term * p_term
  (** Local let. *)
  | P_NLit of int
  (** Natural number literal. *)
  | P_UnaO of unop * p_term
  (** Unary (prefix) operator. *)
  | P_BinO of p_term * binop * p_term
  (** Binary operator. *)
  | P_Wrap of p_term
  (** Parentheses. *)
  | P_Expl of p_term
  (** Explicitly given argument. *)

(** {b NOTE} the boolean parameter of {!constructor:P_Iden} tells whether  the
    corresponding symbol is explicitly applied (value [true]) or not. The flag
    hence indicates whether the symbol has been prefixed with ["@"]. *)

(** Synonym of [p_term] for semantic hints. *)
and p_type = p_term

(** Synonym of [p_term] for semantic hints. *)
and p_patt = p_term

(** [p_get_args t] is {!val:Basics.get_args} on syntax-level terms. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args acc t =
    match t.elt with
    | P_Appl(t, u) -> p_get_args (u::acc) t
    | _            -> (t, acc)
  in p_get_args [] t

(** The previous module provides some functions to create p_term without
    position. *)
module P  =
  struct

    (** [iden s] creates an identifier without position thanks to the string
        [s]. *)
    let iden : string -> p_term = fun s ->
      Pos.none (P_Iden(Pos.none ([], s), true))

    (** [patt s ts] creates a pattern without position thanks to the string
        [s] and the terms [ts]. *)
    let patt : string -> p_term array option -> p_term = fun s ts ->
      Pos.none (P_Patt (Some (Pos.none s), ts))

    (** [patt0 s] creates a pattern without position thanks to the string
        [s]. *)
    let patt0 : string -> p_term = fun s -> patt s None

    (** [appl t1 t2] creates an application of [t1] to [t2] without
        position. *)
    let appl : p_term -> p_term -> p_term = fun t1 t2 ->
      Pos.none (P_Appl(t1, t2))

    (** [appl_list a [b1; ...; bn]] returns (... ((a b1) b2) ...) bn. *)
    let appl_list : p_term -> p_term list -> p_term = List.fold_left appl

    (** [wild] creates a p_term, which represents a wildcard, without
        position. *)
    let wild = Pos.none P_Wild

    (** [appl_wild head i] creates a p_term which has [i] wildcard(s) after
        the head [head]. *)
    let rec appl_wild : p_term -> int -> p_term = fun head i ->
      if i <= 0 then head else appl_wild (appl head wild) (i-1)

    (** [rule] creates a p_rule without position. *)
    let rule : p_patt -> p_term -> p_term p_rule = fun l r -> Pos.none (l,r)

  end

let rec eq_p_term : p_term eq = fun t1 t2 ->
  let module EqAst =
    Syntax.EqAst(struct type t = p_term let eq = eq_p_term end)
  in
  let eq_p_arg = EqAst.eq_p_arg in
  match (t1.elt, t2.elt) with
  | (P_Iden(q1,b1)       , P_Iden(q2,b2)             ) ->
      eq_qident q1 q2 && b1 = b2
  | (P_Meta(x1,ts1)      , P_Meta(x2,ts2)            ) ->
      eq_ident x1 x2 && Option.equal (Array.equal eq_p_term) ts1 ts2
  | (P_Patt(x1,ts1)      , P_Patt(x2,ts2)            ) ->
      Option.equal eq_ident x1 x2
      && Option.equal (Array.equal eq_p_term) ts1 ts2
  | (P_Appl(t1,u1)       , P_Appl(t2,u2)             )
  | (P_Impl(t1,u1)       , P_Impl(t2,u2)             ) ->
      eq_p_term t1 t2 && eq_p_term u1 u2
  | (P_Abst(xs1,t1)      , P_Abst(xs2,t2)            )
  | (P_Prod(xs1,t1)      , P_Prod(xs2,t2)            ) ->
      List.equal eq_p_arg xs1 xs2 && eq_p_term t1 t2
  | (P_LLet(x1,xs1,a1,t1,u1), P_LLet(x2,xs2,a2,t2,u2)) ->
      eq_ident x1 x2 && Option.equal eq_p_term a1 a2 && eq_p_term t1 t2
      && eq_p_term u1 u2 && List.equal eq_p_arg xs1 xs2
  | (P_UnaO(u1,t1)       , P_UnaO(u2,t2)             ) ->
      eq_unop u1 u2 && eq_p_term t1 t2
  | (P_BinO(t1,b1,u1)    , P_BinO(t2,b2,u2)          ) ->
      eq_binop b1 b2 && eq_p_term t1 t2 && eq_p_term u1 u2
  | (P_Wrap(t1)          , P_Wrap(t2)                ) ->
      eq_p_term t1 t2
  | (P_Expl(t1)          , P_Expl(t2)                ) ->
      eq_p_term t1 t2
  | (t1                  ,                   t2      ) ->
      t1 = t2

(** Parser terms with equalities on commands and structures. *)
module Eq = Syntax.EqAst(struct
    type t = p_term
    let eq = eq_p_term
  end)
