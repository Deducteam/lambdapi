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
  | P_Abst of p_term p_args list * p_term
  (** Abstraction over several variables. *)
  | P_Prod of p_term p_args list * p_term
  (** Product over several variables. *)
  | P_LLet of ident * p_term p_args list * p_type option * p_term * p_term
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

(** Parser-level rewriting rule representation. *)
type p_rule = (p_term * p_term) loc

(** [p_get_args t] is {!val:Basics.get_args} on syntax-level terms. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args acc t =
    match t.elt with
    | P_Appl(t, u) -> p_get_args (u::acc) t
    | _            -> (t, acc)
  in p_get_args [] t

(** Module to create p_term's with no positions. *)
module P  =
  struct

    let iden : string -> p_term = fun s ->
      Pos.none (P_Iden(Pos.none ([], s), true))

    let patt : string -> p_term array option -> p_term = fun s ts ->
      Pos.none (P_Patt (Some (Pos.none s), ts))

    let patt0 : string -> p_term = fun s -> patt s None

    let appl : p_term -> p_term -> p_term = fun t1 t2 ->
      Pos.none (P_Appl(t1, t2))

    let appl_list : p_term -> p_term list -> p_term = List.fold_left appl

    let wild = Pos.none P_Wild

    let rec appl_wild : p_term -> int -> p_term = fun head i ->
      if i <= 0 then head else appl_wild (appl head wild) (i-1)

    let abst : ident option -> p_term -> p_term = fun idopt t ->
      Pos.none (P_Abst([[idopt], None, false], t))

    let abst_list : ident option list -> p_term -> p_term = fun idopts t ->
      List.fold_right abst idopts t

    let rule : p_patt -> p_term -> p_rule = fun l r -> Pos.none (l,r)
  end

(** [eq] is an equality function on parser level terms [t1] and [t2]. *)
let rec eq_p_term: p_term eq = fun t1 t2 ->
  (* We define this function recursively using the equality defined on
     arguments by the modules of {!module:Syntax}. *)
  let module EqAst =
    EqAst (struct type t = p_term let eq = eq_p_term end)
      (struct type t = p_rule let eq = eq_p_rule end)
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

(** [eq_p_rule] is an equality function between parser level rules. *)
and eq_p_rule : p_rule eq = fun {elt=(lhs1,rhs1);_} {elt=(lhs2,rhs2);_} ->
  eq_p_term lhs1 lhs2 && eq_p_term rhs1 rhs2

(** Parser terms with equalities on commands and structures. Defined after
    [eq_p_term] and [eq_p_rule] because we cannot have mutual recursive
    definitions of modules and functions. *)
module Eq =
  Syntax.EqAst
    (struct type t = p_term let eq = eq_p_term end)
    (struct type t = p_rule let eq = eq_p_rule end)

(** [pp oc t] prints parser term [t] to out channel [oc]. *)
let rec pp : p_term pp = fun oc t ->
  let module Ptp =
    Pretty.Make
      (struct type t = p_term let pp = pp end)
      (struct type t = p_rule let pp = pp_p_rule end)
  in
  let out fmt = Format.fprintf oc fmt in
  let empty_context = ref true in
  let rec pp p _ t =
    let env _ ar =
      match ar with
      | None -> ()
      | Some [||] when !empty_context -> ()
      | Some ar -> out "[%a]" (Array.pp (pp `PFunc) "; ") ar
    in
    let atom = pp `PAtom in
    match (t.elt, p) with
    | (P_Type              , _    ) -> out "TYPE"
    | (P_Iden(qid, _)      , _    ) -> out "%a" Pretty.qident qid
    | (P_Wild              , _    ) -> out "_"
    | (P_Meta(x,ar)        , _    ) -> out "?%a%a" Pretty.ident x env ar
    | (P_Patt(None   ,ar)  , _    ) -> out "$_%a" env ar
    | (P_Patt(Some(x),ar)  , _    ) -> out "$%a%a" Pretty.ident x env ar
    | (P_Appl(t,u)         , `PAppl)
    | (P_Appl(t,u)         , `PFunc) -> out "%a %a" appl t atom u
    | (P_Impl(a,b)         , `PFunc) -> out "%a → %a" appl a func b
    | (P_Abst(xs,t)        , `PFunc) ->
        out "λ%a, " Ptp.args_list xs;
        let fn (ids,_,_) = List.for_all ((=) None) ids in
        let ec = !empty_context in
        empty_context := ec && List.for_all fn xs;
        out "%a" func t;
        empty_context := ec
    | (P_Prod(xs,b)        , `PFunc) ->
        out "Π%a, %a" Ptp.args_list xs func b
    | (P_LLet(x,xs,a,t,u), `PFunc)   ->
        out "@[<hov 2>let %a%a%a ≔@ %a@] in %a"
          Pretty.ident x Ptp.args_list xs Ptp.annot a
          func t func u
    | (P_NLit(i)           , _    ) -> out "%i" i
    | (P_UnaO((u,_,_),t)   , _    ) -> out "(%s %a)" u atom t
    | (P_BinO(t,(b,_,_,_),u), _    ) -> out "(%a %s %a)" atom t b atom u
    (* We print minimal parentheses, and ignore the [Wrap] constructor. *)
    | (P_Wrap(t)           , _    ) -> out "%a" (pp p) t
    | (P_Expl(t)           , _    ) -> out "{%a}" func t
    | (_                   , _    ) -> out "(%a)" func t
  and appl oc t = pp `PAppl oc t
  and func oc t = pp `PFunc oc t in
  let rec toplevel _ t =
    match t.elt with
    | P_Abst(args,t)       -> out "λ%a, %a" Ptp.args_list args toplevel t
    | P_Prod(args,b)       -> out "Π%a, %a" Ptp.args_list args toplevel b
    | P_Impl(a,b)          -> out "%a → %a" appl a toplevel b
    | P_LLet(x,xs,a,t,u) ->
        out "@[<hov 2>let %a%a%a ≔ %a@] in %a" Pretty.ident x
          Ptp.args_list xs Ptp.annot a toplevel t toplevel u
    | _                    -> out "%a" func t
  in
  toplevel oc t

and pp_p_rule : p_rule pp = fun oc {elt=(lhs,rhs);_} ->
  Format.fprintf oc "@[<hov 3>%a ↪ %a@]@?" pp lhs pp rhs

(** [Pp] provides printing functions for {!type:P_terms.p_term} commands. *)
module Pp =
  Pretty.Make
    (struct type t = p_term let pp = pp end)
    (struct type t = p_rule let pp = pp_p_rule end)

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : (p_term, p_rule) ast -> unit = Pp.ast Format.std_formatter
