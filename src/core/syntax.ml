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

(** Parser-level representation of modifiers. *)
type p_modifier =
  | P_mstrat of Terms.match_strat
  | P_expo of Terms.expo
  | P_prop of Terms.prop

(** Type representing the different evaluation strategies. *)
type strategy =
  | WHNF
  (** Reduce to weak head-normal form. *)
  | HNF
  (** Reduce to head-normal form. *)
  | SNF
  (** Reduce to strong normal form. *)
  | NONE
  (** Do nothing. *)

(** Representation of the associativity of an infix operator. *)
type assoc =
  | Assoc_none
  | Assoc_left
  | Assoc_right

(** The priority of an infix operator is a floating-point number. *)
type priority = float

(** Representation of a unary operator. *)
type unop = string * priority * qident

(** Representation of a binary operator. *)
type binop = string * assoc * priority * qident

(** Parser-level representation of a function argument. The boolean is true if
    the argument is marked as implicit (i.e., between curly braces). *)
type 'term p_arg = ident option list * 'term option * bool

(** Parser-level rewriting rule representation. *)
type 'term p_rule = ('term * 'term) loc

(** Parser-level inductive type representation. *)
type 'term p_inductive = (ident * 'term * (ident * 'term) list) loc

(** Rewrite pattern specification. *)
type 'term p_rw_patt =
  | P_rw_Term           of 'term
  | P_rw_InTerm         of 'term
  | P_rw_InIdInTerm     of ident * 'term
  | P_rw_IdInTerm       of ident * 'term
  | P_rw_TermInIdInTerm of 'term * ident * 'term
  | P_rw_TermAsIdInTerm of 'term * ident * 'term

(** Parser-level representation of an assertion. *)
type 'term p_assertion =
  | P_assert_typing of 'term * 'term
  (** The given term should have the given type. *)
  | P_assert_conv   of 'term * 'term
  (** The two given terms should be convertible. *)

(** Configuration for evaluation. *)
type eval_config =
  { strategy : strategy   (** Evaluation strategy.          *)
  ; steps    : int option (** Max number of steps if given. *) }

(** Parser-level representation of a query command. *)
type 'term p_query_aux =
  | P_query_verbose   of int
  (** Sets the verbosity level. *)
  | P_query_debug     of bool * string
  (** Toggles logging functions described by string according to boolean. *)
  | P_query_flag      of string * bool
  (** Sets the boolean flag registered under the given name (if any). *)
  | P_query_assert    of bool * 'term p_assertion
  (** Assertion (must fail if boolean is [true]). *)
  | P_query_infer     of 'term * eval_config
  (** Type inference command. *)
  | P_query_normalize of 'term * eval_config
  (** Normalisation command. *)
  | P_query_prover    of string
  (** Set the prover to use inside a proof. *)
  | P_query_prover_timeout of int
  (** Set the timeout of the prover (in seconds). *)

type 'term p_query = 'term p_query_aux loc

(** Parser-level representation of a proof tactic. *)
type 'term p_tactic_aux =
  | P_tac_refine  of 'term
  (** Refine the current goal using the given term. *)
  | P_tac_intro   of ident option list
  (** Eliminate quantifiers using the given names for hypotheses. *)
  | P_tac_apply   of 'term
  (** Apply the given term to the current goal. *)
  | P_tac_simpl
  (** Normalize in the focused goal. *)
  | P_tac_rewrite of bool * 'term p_rw_patt loc option * 'term
  (** Apply rewriting using the given pattern and equational proof. The
     boolean indicates whether the equation has to be applied from left to
     right. *)
  | P_tac_refl
  (** Apply reflexivity of equality. *)
  | P_tac_sym
  (** Apply symmetry of equality. *)
  | P_tac_focus   of int
  (** Focus on the given goal. *)
  | P_tac_print
  (** Print the current goal. *)
  | P_tac_proofterm
  (** Print the current proof term (possibly containing open goals). *)
  | P_tac_why3 of string option
  (** Try to solve the current goal with why3. *)
  | P_tac_query   of 'term p_query
  (** Query. *)
  | P_tac_fail
  (** A tactic that always fails. *)

type 'term p_tactic = 'term p_tactic_aux loc

(** Parser-level representation of a proof terminator. *)
type p_proof_end =
  | P_proof_qed
  (** The proof is done and fully checked. *)
  | P_proof_admit
  (** Give up current state and admit the theorem. *)
  | P_proof_abort
  (** Abort the proof (theorem not admitted). *)

(** Parser-level representation of a configuration command. *)
type 'term p_config =
  | P_config_builtin   of string * qident
  (** Sets the configuration for a builtin syntax (e.g., nat literals). *)
  | P_config_unop      of unop
  (** Defines (or redefines) a unary operator (e.g., ["!"] or ["¬"]). *)
  | P_config_binop     of binop
  (** Defines (or redefines) a binary operator (e.g., ["+"] or ["×"]). *)
  | P_config_ident     of string
  (** Defines a new, valid identifier (e.g., ["σ"], ["€"] or ["ℕ"]). *)
  | P_config_quant of qident
  (** Defines a quantifier symbol (e.g., ["∀"], ["∃"]). *)
  | P_config_unif_rule of 'term p_rule
  (** Unification hint declarations. *)

(** Parser-level representation of a single command. *)
type 'term p_statement = (ident * 'term p_arg list * 'term) loc

type 'term p_command_aux =
  | P_require    of bool * p_module_path list
  (** Require statement (require open if the boolean is true). *)
  | P_require_as of p_module_path * (string * bool) loc
  (** Require as statement. *)
  | P_open       of p_module_path list
  (** Open statement. *)
  | P_symbol     of p_modifier loc list * ident * 'term p_arg list * 'term
  (** Symbol declaration. *)
  | P_rules      of 'term p_rule list
  (** Rewriting rule declarations. *)
  | P_definition of p_modifier loc list * bool * ident * 'term p_arg list *
                    'term option * 'term
  (** Definition of a symbol (unfoldable). *)
  | P_inductive of p_modifier loc list * 'term p_inductive list
  (** Definition of inductive type *)
  | P_theorem    of p_modifier loc list * 'term p_statement * 'term p_tactic list *
                    p_proof_end loc
  (** Theorem with its proof. *)
  | P_set        of 'term p_config
  (** Set the configuration. *)
  | P_query      of 'term p_query
  (** Query. *)

(** Parser-level representation of a single (located) command. *)
type 'term p_command = 'term p_command_aux loc

(** Top level AST returned by the parser. *)
type 'term ast = 'term p_command list

let eq_ident : ident eq = fun x1 x2 -> x1.elt = x2.elt

let eq_qident : qident eq = fun q1 q2 -> q1.elt = q2.elt

let eq_unop : unop eq = fun (n1,p1,id1) (n2,p2,id2) ->
  n1 = n2 && p1 = p2 && eq_qident id1 id2

let eq_binop : binop eq = fun (n1,a1,p1,id1) (n2,a2,p2,id2) ->
  n1 = n2 && a1 = a2 && p1 = p2 && eq_qident id1 id2

(** Equality functions parametrised by terms and equality on terms. *)
module EqAst (T: sig type t val eq : t eq end) = struct

  let eq_p_arg : T.t p_arg eq = fun (x1,ao1,b1) (x2,ao2,b2) ->
    List.equal (Option.equal (fun x1 x2 -> x1.elt = x2.elt)) x1 x2
    && Option.equal T.eq ao1 ao2 && b1 = b2

  let eq_p_rule : T.t p_rule eq = fun r1 r2 ->
    let {elt = (lhs1, rhs1); _} = r1 in
    let {elt = (lhs2, rhs2); _} = r2 in
    T.eq lhs1 lhs2 && T.eq rhs1 rhs2

  let eq_p_rw_patt : T.t p_rw_patt loc eq = fun r1 r2 ->
    match (r1.elt, r2.elt) with
    | (P_rw_Term(t1)                , P_rw_Term(t2)                )
    | (P_rw_InTerm(t1)              , P_rw_InTerm(t2)              ) ->
        T.eq t1 t2
    | (P_rw_InIdInTerm(x1,t1)       , P_rw_InIdInTerm(x2,t2)       )
    | (P_rw_IdInTerm(x1,t1)         , P_rw_IdInTerm(x2,t2)         ) ->
        eq_ident x1 x2 && T.eq t1 t2
    | (P_rw_TermInIdInTerm(t1,x1,u1), P_rw_TermInIdInTerm(t2,x2,u2))
    | (P_rw_TermAsIdInTerm(t1,x1,u1), P_rw_TermAsIdInTerm(t2,x2,u2)) ->
        eq_ident x1 x2 && T.eq t1 t2 && T.eq u1 u2
    | (_                            , _                            ) ->
        false

  let eq_p_inductive : T.t p_inductive eq = fun i1 i2 ->
    let {elt = (s1, t1, tl1); _} = i1 in
    let {elt = (s2, t2, tl2); _} = i2 in
    let eq_id_p_term (s1,t1) (s2,t2) = eq_ident s1 s2 && T.eq t1 t2 in
    List.equal eq_id_p_term ((s1,t1)::tl1) ((s2,t2)::tl2)

  let eq_p_assertion : T.t p_assertion eq = fun a1 a2 ->
    match (a1, a2) with
    | (P_assert_typing(t1,a1), P_assert_typing(t2,a2)) ->
        T.eq t1 t2 && T.eq a1 a2
    | (P_assert_conv(t1,u1)  , P_assert_conv(t2,u2)  ) ->
        T.eq t1 t2 && T.eq u1 u2
    | (_                     , _                     ) ->
        false

  let eq_p_query : T.t p_query eq = fun q1 q2 ->
    match (q1.elt, q2.elt) with
    | (P_query_assert(b1,a1)     , P_query_assert(b2,a2)     ) ->
       b1 = b2 && eq_p_assertion a1 a2
    | (P_query_infer(t1,c1)      , P_query_infer(t2,c2)      ) ->
       T.eq t1 t2 && c1 = c2
    | (P_query_normalize(t1,c1)  , P_query_normalize(t2,c2)  ) ->
       T.eq t1 t2 && c1 = c2
    | (P_query_prover(s1)        , P_query_prover(s2)        ) ->
       s1 = s2
    | (P_query_prover_timeout(t1), P_query_prover_timeout(t2)) ->
       t1 = t2
    | (_                         , _                         ) ->
        false

  let eq_p_tactic : T.t p_tactic eq = fun t1 t2 ->
    match (t1.elt, t2.elt) with
    | (P_tac_refine(t1)    , P_tac_refine(t2)    ) ->
        T.eq t1 t2
    | (P_tac_intro(xs1)    , P_tac_intro(xs2)    ) ->
        List.equal (Option.equal eq_ident) xs1 xs2
    | (P_tac_apply(t1)     , P_tac_apply(t2)     ) ->
        T.eq t1 t2
    | (P_tac_rewrite(b1,r1,t1), P_tac_rewrite(b2,r2,t2)) ->
        b1 = b2 && Option.equal eq_p_rw_patt r1 r2 && T.eq t1 t2
    | (P_tac_query(q1)     , P_tac_query(q2)     ) ->
        eq_p_query q1 q2
    | (P_tac_why3(s1)      , P_tac_why3(s2)      ) ->
        s1 = s2
    | (t1                  , t2                  ) ->
        t1 = t2

  let eq_p_config : T.t p_config eq = fun c1 c2 ->
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

  (** [eq_command c1 c2] tells whether [c1] and [c2] are the same commands.
      They are compared up to source code positions. *)
  let eq_p_command : T.t p_command eq = fun c1 c2 ->
    match (c1.elt, c2.elt) with
    | (P_require(b1,ps1)           , P_require(b2,ps2)           ) ->
       b1 = b2 && List.equal (=) ps1 ps2
    | (P_open(ps1)                 , P_open(ps2)                 ) ->
       List.equal (=) ps1 ps2
    | (P_require_as(p1,id1)  , P_require_as(p2,id2)              ) ->
       p1 = p2 && id1.elt = id2.elt
    | (P_symbol(m1,s1,al1,a1), P_symbol(m2,s2,al2,a2)) ->
        m1 = m2 && eq_ident s1 s2 && T.eq a1 a2
        && List.equal eq_p_arg al1 al2
    | (P_rules(rs1)                , P_rules(rs2)                ) ->
        List.equal eq_p_rule rs1 rs2
    | (P_definition(m1,b1,s1,l1,a1,t1), P_definition(m2,b2,s2,l2,a2,t2)) ->
        m1 = m2 && b1 = b2 && eq_ident s1 s2 && List.equal eq_p_arg l1 l2
        && Option.equal T.eq a1 a2 && T.eq t1 t2
    | (P_inductive(m1,i1), P_inductive(m2, i2)) ->
        m1 = m2 && List.equal eq_p_inductive i1 i2
    | (P_theorem(m1,st1,ts1,e1)   , P_theorem(m2,st2,ts2,e2)   ) ->
        let (s1,l1,a1) = st1.elt in
        let (s2,l2,a2) = st2.elt in
        m1 = m2 && eq_ident s1 s2 && T.eq a1 a2 && e1.elt = e2.elt
        && List.equal eq_p_arg l1 l2 && List.equal eq_p_tactic ts1 ts2
    | (P_set(c1)                   , P_set(c2)                   ) ->
        eq_p_config c1 c2
    | (P_query(q1)                 , P_query(q2)                 ) ->
        eq_p_query q1 q2
    | (_                           , _                           ) ->
        false
end
