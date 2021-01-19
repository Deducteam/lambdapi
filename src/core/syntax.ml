(** Parser-level abstract syntax. *)

open Lplib
open Lplib.Base

open Pos

(** Representation of a (located) identifier. *)
type ident = strloc

(** Parsing representation of a module path. For every path member the boolean
    indicates whether it was given using the escaped syntax. *)
type p_module_path = (string * bool) list

(** Representation of a possibly qualified (and located) identifier. *)
type qident = (p_module_path * string) loc

(** The priority of an infix operator is a floating-point number. *)
type priority = float

(** Representation of a unary operator. *)
type unop = string * priority * qident

(** Representation of a binary operator. *)
type binop = string * Pratter.associativity * priority * qident

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
  | P_Abst of p_args list * p_term
  (** Abstraction over several variables. *)
  | P_Prod of p_args list * p_term
  (** Product over several variables. *)
  | P_LLet of ident * p_args list * p_type option * p_term * p_term
  (** Local let. *)
  | P_NLit of int
  (** Natural number literal. *)
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

(** Parser-level representation of a function argument. The boolean is true if
    the argument is marked as implicit (i.e., between curly braces). *)
and p_args = ident option list * p_type option * bool

(** [p_get_args t] is {!val:Basics.get_args} on syntax-level terms. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args acc t =
    match t.elt with
    | P_Appl(t, u) -> p_get_args (u::acc) t
    | _            -> (t, acc)
  in p_get_args [] t

(** Parser-level rewriting rule representation. *)
type p_rule = (p_patt * p_term) loc

(** Parser-level inductive type representation. *)
type p_inductive = (ident * p_term * (ident * p_term) list) loc

(** Module to create p_term's with no positions. *)
module P  = struct
  let iden : string -> p_term = fun s ->
    Pos.none (P_Iden(Pos.none ([], s), true))

  let patt : string -> p_term array option -> p_term = fun s ts ->
    Pos.none (P_Patt (Some (Pos.none s), ts))

  let patt0 : string -> p_term = fun s -> patt s None

  let appl : p_term -> p_term -> p_term = fun t1 t2 ->
    Pos.none (P_Appl(t1, t2))

  let appl_list : p_term -> p_term list -> p_term = List.fold_left appl

  let wild = Pos.none P_Wild

  let rec appl_wild : p_term -> int -> p_term = fun t i ->
      if i <= 0 then t else appl_wild (appl t wild) (i-1)

  let abst : ident option -> p_term -> p_term = fun idopt t ->
    Pos.none (P_Abst([[idopt],None,false], t))

  let abst_list : ident option list -> p_term -> p_term = fun idopts t ->
    List.fold_right abst idopts t

  let rule : p_patt -> p_term -> p_rule = fun l r -> Pos.none (l,r)
end

(** Rewrite pattern specification. *)
type p_rw_patt =
  | P_rw_Term           of p_term
  | P_rw_InTerm         of p_term
  | P_rw_InIdInTerm     of ident * p_term
  | P_rw_IdInTerm       of ident * p_term
  | P_rw_TermInIdInTerm of p_term * ident * p_term
  | P_rw_TermAsIdInTerm of p_term * ident * p_term

(** Parser-level representation of an assertion. *)
type p_assertion =
  | P_assert_typing of p_term * p_type
  (** The given term should have the given type. *)
  | P_assert_conv   of p_term * p_term
  (** The two given terms should be convertible. *)

(** Type representing the different evaluation strategies. *)
type strategy =
  | WHNF (** Reduce to weak head-normal form. *)
  | HNF  (** Reduce to head-normal form. *)
  | SNF  (** Reduce to strong normal form. *)
  | NONE (** Do nothing. *)

(** Configuration for evaluation. *)
type eval_config =
  { strategy : strategy   (** Evaluation strategy.          *)
  ; steps    : int option (** Max number of steps if given. *) }

(** Parser-level representation of a query command. *)
type p_query_aux =
  | P_query_verbose of int
  (** Sets the verbosity level. *)
  | P_query_debug of bool * string
  (** Toggles logging functions described by string according to boolean. *)
  | P_query_flag of string * bool
  (** Sets the boolean flag registered under the given name (if any). *)
  | P_query_assert of bool * p_assertion
  (** Assertion (must fail if boolean is [true]). *)
  | P_query_infer of p_term * eval_config
  (** Type inference command. *)
  | P_query_normalize of p_term * eval_config
  (** Normalisation command. *)
  | P_query_prover of string
  (** Set the prover to use inside a proof. *)
  | P_query_prover_timeout of int
  (** Set the timeout of the prover (in seconds). *)
  | P_query_print of qident option
  (** Print information about a symbol or the current goals. *)
  | P_query_proofterm
  (** Print the current proof term (possibly containing open goals). *)

type p_query = p_query_aux loc

(** Parser-level representation of a proof tactic. *)
type p_tactic_aux =
  | P_tac_refine of p_term
  (** Refine the current goal using the given term. *)
  | P_tac_intro of ident option list
  (** Eliminate quantifiers using the given names for hypotheses. *)
  | P_tac_apply of p_term
  (** Apply the given term to the current goal. *)
  | P_tac_simpl
  (** Normalize in the focused goal. *)
  | P_tac_rewrite of bool * p_rw_patt loc option * p_term
  (** Apply rewriting using the given pattern and equational proof. The
     boolean indicates whether the equation has to be applied from left to
     right. *)
  | P_tac_refl
  (** Apply reflexivity of equality. *)
  | P_tac_sym
  (** Apply symmetry of equality. *)
  | P_tac_focus of int
  (** Focus on the given goal. *)
  | P_tac_why3 of string option
  (** Try to solve the current goal with why3. *)
  | P_tac_solve
  (** Apply default unification solving algorithm. *)
  | P_tac_query of p_query
  (** Query. *)
  | P_tac_fail
  (** A tactic that always fails. *)

type p_tactic = p_tactic_aux loc

(** Parser-level representation of a proof terminator. *)
type p_proof_end_aux =
  | P_proof_end
  (** The proof is done and fully checked. *)
  | P_proof_admit
  (** Give up current state and admit the theorem. *)
  | P_proof_abort
  (** Abort the proof (theorem not admitted). *)

type p_proof_end = p_proof_end_aux loc

(** Parser-level representation of a configuration command. *)
type p_config =
  | P_config_builtin of string * qident
  (** Sets the configuration for a builtin syntax (e.g., nat literals). *)
  | P_config_unop of unop
  (** Defines (or redefines) a unary operator (e.g., ["!"] or ["¬"]). *)
  | P_config_binop of binop
  (** Defines (or redefines) a binary operator (e.g., ["+"] or ["×"]). *)
  | P_config_quant of qident
  (** Defines a quantifier symbol (e.g., ["∀"], ["∃"]). *)
  | P_config_unif_rule of p_rule
  (** Unification hint declarations. *)

(** Parser-level representation of modifiers. *)
type p_modifier_aux =
  | P_mstrat of Terms.match_strat (** pattern matching strategy *)
  | P_expo of Terms.expo (** visibility of symbol outside its modules *)
  | P_prop of Terms.prop (** symbol properties : constant, definable, ... *)
  | P_opaq (** opacity *)

type p_modifier = p_modifier_aux loc

let is_prop {elt; _} = match elt with P_prop(_) -> true | _ -> false
let is_opaq {elt; _} = match elt with P_opaq -> true | _ -> false
let is_expo {elt; _} = match elt with P_expo(_) -> true | _ -> false
let is_mstrat {elt; _} = match elt with P_mstrat(_) -> true | _ -> false

(** Parser-level representation of symbol declarations. *)
type p_symbol =
  { p_sym_mod : p_modifier list (** modifiers *)
  ; p_sym_nam : ident (** symbol name *)
  ; p_sym_arg : p_args list (** arguments before ":" *)
  ; p_sym_typ : p_type option (** symbol type *)
  ; p_sym_trm : p_term option (** symbol definition *)
  ; p_sym_prf : (p_tactic list * p_proof_end) option (** proof script *)
  ; p_sym_def : bool (** is the symbol defined ? *) }

(** Parser-level representation of a single command. *)
type p_command_aux =
  | P_require  of bool * p_module_path list
  (** Require statement (require open if the boolean is true). *)
  | P_require_as of p_module_path * (string * bool) loc
  (** Require as statement. *)
  | P_open of p_module_path list
  (** Open statement. *)
  | P_symbol of p_symbol
  (** Symbol declaration. *)
  | P_rules of p_rule list
  (** Rewriting rule declarations. *)
  | P_inductive of p_modifier list * p_inductive list
  (** Definition of inductive types *)
  | P_set of p_config
  (** Set the configuration. *)
  | P_query of p_query
  (** Query. *)

(** Parser-level representation of a single (located) command. *)
type p_command = p_command_aux loc

(** Top level AST returned by the parser. *)
type ast = p_command Stream.t

let eq_ident : ident eq = fun x1 x2 -> x1.elt = x2.elt

let eq_qident : qident eq = fun q1 q2 -> q1.elt = q2.elt

let eq_unop : unop eq = fun (n1,p1,id1) (n2,p2,id2) ->
  n1 = n2 && p1 = p2 && eq_qident id1 id2

let eq_binop : binop eq = fun (n1,a1,p1,id1) (n2,a2,p2,id2) ->
  n1 = n2 && a1 = a2 && p1 = p2 && eq_qident id1 id2

let rec eq_p_term : p_term eq = fun t1 t2 ->
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
      List.equal eq_p_args xs1 xs2 && eq_p_term t1 t2
  | (P_LLet(x1,xs1,a1,t1,u1), P_LLet(x2,xs2,a2,t2,u2)) ->
      eq_ident x1 x2 && Option.equal eq_p_term a1 a2 && eq_p_term t1 t2
      && eq_p_term u1 u2 && List.equal eq_p_args xs1 xs2
  | (P_Wrap(t1)          , P_Wrap(t2)                ) ->
      eq_p_term t1 t2
  | (P_Expl(t1)          , P_Expl(t2)                ) ->
      eq_p_term t1 t2
  | (t1                  ,                   t2      ) ->
      t1 = t2

and eq_p_args : p_args eq = fun (x1,ao1,b1) (x2,ao2,b2) ->
  List.equal (Option.equal (fun x1 x2 -> x1.elt = x2.elt)) x1 x2
  && Option.equal eq_p_term ao1 ao2 && b1 = b2

let eq_p_rule : p_rule eq = fun r1 r2 ->
  let {elt = (lhs1, rhs1); _} = r1 in
  let {elt = (lhs2, rhs2); _} = r2 in
  eq_p_term lhs1 lhs2 && eq_p_term rhs1 rhs2

let eq_p_inductive : p_inductive eq = fun i1 i2 ->
  let {elt = (s1, t1, tl1); _} = i1 in
  let {elt = (s2, t2, tl2); _} = i2 in
  let eq_id_p_term (s1,t1) (s2,t2) = eq_ident s1 s2 && eq_p_term t1 t2 in
  List.equal eq_id_p_term ((s1,t1)::tl1) ((s2,t2)::tl2)

let eq_p_rw_patt : p_rw_patt loc eq = fun r1 r2 ->
  match (r1.elt, r2.elt) with
  | (P_rw_Term(t1)                , P_rw_Term(t2)                )
  | (P_rw_InTerm(t1)              , P_rw_InTerm(t2)              ) ->
      eq_p_term t1 t2
  | (P_rw_InIdInTerm(x1,t1)       , P_rw_InIdInTerm(x2,t2)       )
  | (P_rw_IdInTerm(x1,t1)         , P_rw_IdInTerm(x2,t2)         ) ->
      eq_ident x1 x2 && eq_p_term t1 t2
  | (P_rw_TermInIdInTerm(t1,x1,u1), P_rw_TermInIdInTerm(t2,x2,u2))
  | (P_rw_TermAsIdInTerm(t1,x1,u1), P_rw_TermAsIdInTerm(t2,x2,u2)) ->
      eq_ident x1 x2 && eq_p_term t1 t2 && eq_p_term u1 u2
  | (_                            , _                            ) ->
      false

let eq_p_assertion : p_assertion eq = fun a1 a2 ->
  match (a1, a2) with
  | (P_assert_typing(t1,a1), P_assert_typing(t2,a2)) ->
      eq_p_term t1 t2 && eq_p_term a1 a2
  | (P_assert_conv(t1,u1)  , P_assert_conv(t2,u2)  ) ->
      eq_p_term t1 t2 && eq_p_term u1 u2
  | (_                     , _                     ) ->
      false

let eq_p_query : p_query eq = fun q1 q2 ->
  match (q1.elt, q2.elt) with
  | (P_query_assert(b1,a1)     , P_query_assert(b2,a2)     ) ->
     b1 = b2 && eq_p_assertion a1 a2
  | (P_query_infer(t1,c1)      , P_query_infer(t2,c2)      ) ->
     eq_p_term t1 t2 && c1 = c2
  | (P_query_normalize(t1,c1)  , P_query_normalize(t2,c2)  ) ->
     eq_p_term t1 t2 && c1 = c2
  | (P_query_prover(s1)        , P_query_prover(s2)        ) ->
     s1 = s2
  | (P_query_prover_timeout(t1), P_query_prover_timeout(t2)) ->
     t1 = t2
  | (P_query_print(s1)         , P_query_print(s2)         ) ->
     Option.equal eq_qident s1 s2
  | (_                         , _                         ) ->
      false

let eq_p_tactic : p_tactic eq = fun t1 t2 ->
  match (t1.elt, t2.elt) with
  | (P_tac_refine(t1)    , P_tac_refine(t2)    ) ->
      eq_p_term t1 t2
  | (P_tac_intro(xs1)    , P_tac_intro(xs2)    ) ->
      List.equal (Option.equal eq_ident) xs1 xs2
  | (P_tac_apply(t1)     , P_tac_apply(t2)     ) ->
      eq_p_term t1 t2
  | (P_tac_rewrite(b1,r1,t1), P_tac_rewrite(b2,r2,t2)) ->
      b1 = b2 && Option.equal eq_p_rw_patt r1 r2 && eq_p_term t1 t2
  | (P_tac_query(q1)     , P_tac_query(q2)     ) ->
      eq_p_query q1 q2
  | (P_tac_why3(s1)      , P_tac_why3(s2)      ) ->
      s1 = s2
  | (t1                  , t2                  ) ->
      t1 = t2

let eq_p_config : p_config eq = fun c1 c2 ->
  match (c1, c2) with
  | (P_config_builtin(s1,q1), P_config_builtin(s2,q2)) ->
      s1 = s2 && eq_qident q1 q2
  | (P_config_unop u1       , P_config_unop u2       ) ->
      eq_unop u1 u2
  | (P_config_binop b1      , P_config_binop b2      ) ->
      eq_binop b1 b2
  | (P_config_quant q1      , P_config_quant q2      ) ->
      eq_qident q1 q2
  | (c1                     , c2                     ) ->
      c1 = c2

let eq_p_symbol : p_symbol eq = fun
    { p_sym_mod=p_sym_mod1; p_sym_nam=p_sym_nam1; p_sym_arg=p_sym_arg1;
      p_sym_typ=p_sym_typ1; p_sym_trm=p_sym_trm1; p_sym_prf=p_sym_prf1;
      p_sym_def=p_sym_def1}
    { p_sym_mod=p_sym_mod2; p_sym_nam=p_sym_nam2; p_sym_arg=p_sym_arg2;
      p_sym_typ=p_sym_typ2; p_sym_trm=p_sym_trm2; p_sym_prf=p_sym_prf2;
      p_sym_def=p_sym_def2} ->
  p_sym_mod1 = p_sym_mod2
  && eq_ident p_sym_nam1 p_sym_nam2
  && List.equal eq_p_args p_sym_arg1 p_sym_arg2
  && Option.equal eq_p_term p_sym_typ1 p_sym_typ2
  && Option.equal eq_p_term p_sym_trm1 p_sym_trm2
  && let eq_tac (ts1,_) (ts2,_) = List.equal eq_p_tactic ts1 ts2 in
     Option.equal eq_tac p_sym_prf1 p_sym_prf2
  && p_sym_def1 = p_sym_def2

(** [eq_command c1 c2] tells whether [c1] and [c2] are the same commands. They
    are compared up to source code positions. *)
let eq_p_command : p_command eq = fun c1 c2 ->
  match (c1.elt, c2.elt) with
  | (P_require(b1,ps1)           , P_require(b2,ps2)           ) ->
     b1 = b2 && List.equal (=) ps1 ps2
  | (P_open(ps1)                 , P_open(ps2)                 ) ->
     List.equal (=) ps1 ps2
  | (P_require_as(p1,id1)  , P_require_as(p2,id2)              ) ->
     p1 = p2 && id1.elt = id2.elt
  | (P_symbol s1                 , P_symbol s2                 ) ->
      eq_p_symbol s1 s2
  | (P_rules(rs1)                , P_rules(rs2)                ) ->
      List.equal eq_p_rule rs1 rs2
  | (P_inductive(m1,il1)         , P_inductive(m2,il2)         ) ->
      m1 = m2 && List.equal eq_p_inductive il1 il2
  | (P_set(c1)                   , P_set(c2)                   ) ->
      eq_p_config c1 c2
  | (P_query(q1)                 , P_query(q2)                 ) ->
      eq_p_query q1 q2
  | (_                           , _                           ) ->
      false
