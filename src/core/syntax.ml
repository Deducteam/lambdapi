(** Parser-level abstract syntax. *)

open Lplib
open Lplib.Base

open Pos

(** Set of identifier characters. *)
let id_charset = Earley_core.Charset.from_string "a-zA-Z0-9_'"

(** Keywords module, used by parser and {!module:Pretty}. *)
module KW =
  Earley_core.Keywords.Make(struct
    let id_charset = id_charset
    let reserved = []
  end)

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
type 't p_arg = ident option list * 't option * bool

(** Parser-level inductive type representation. *)
type 'term p_inductive = (ident * 'term * (ident * 'term) list) loc

(** Rewrite pattern specification. *)
type 't p_rw_patt =
  | P_rw_Term           of 't
  | P_rw_InTerm         of 't
  | P_rw_InIdInTerm     of ident * 't
  | P_rw_IdInTerm       of ident * 't
  | P_rw_TermInIdInTerm of 't * ident * 't
  | P_rw_TermAsIdInTerm of 't * ident * 't

(** Parser-level representation of an assertion. *)
type 't p_assertion =
  | P_assert_typing of 't * 't
  (** The given term should have the given type. *)
  | P_assert_conv   of 't * 't
  (** The two given terms should be convertible. *)

(** Configuration for evaluation. *)
type eval_config =
  { strategy : strategy   (** Evaluation strategy.          *)
  ; steps    : int option (** Max number of steps if given. *) }

(** Parser-level representation of a query command. *)
type 't p_query_aux =
  | P_query_verbose   of int
  (** Sets the verbosity level. *)
  | P_query_debug     of bool * string
  (** Toggles logging functions described by string according to boolean. *)
  | P_query_flag      of string * bool
  (** Sets the boolean flag registered under the given name (if any). *)
  | P_query_assert    of bool * 't p_assertion
  (** Assertion (must fail if boolean is [true]). *)
  | P_query_infer     of 't * eval_config
  (** Type inference command. *)
  | P_query_normalize of 't * eval_config
  (** Normalisation command. *)
  | P_query_prover    of string
  (** Set the prover to use inside a proof. *)
  | P_query_prover_timeout of int
  (** Set the timeout of the prover (in seconds). *)

type 't p_query = 't p_query_aux loc

(** Parser-level representation of a proof tactic. *)
type 't p_tactic_aux =
  | P_tac_refine  of 't
  (** Refine the current goal using the given term. *)
  | P_tac_intro   of ident option list
  (** Eliminate quantifiers using the given names for hypotheses. *)
  | P_tac_apply   of 't
  (** Apply the given term to the current goal. *)
  | P_tac_simpl
  (** Normalize in the focused goal. *)
  | P_tac_rewrite of bool * 't p_rw_patt loc option * 't
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
  | P_tac_query   of 't p_query
  (** Query. *)
  | P_tac_fail
  (** A tactic that always fails. *)

type 't p_tactic = 't p_tactic_aux loc

(** Parser-level representation of a proof terminator. *)
type p_proof_end =
  | P_proof_qed
  (** The proof is done and fully checked. *)
  | P_proof_admit
  (** Give up current state and admit the theorem. *)
  | P_proof_abort
  (** Abort the proof (theorem not admitted). *)

(** Parser-level representation of a configuration command. *)
type 'r p_config =
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
  | P_config_unif_rule of 'r
  (** Unification hint declarations. *)

(** Parser-level representation of a single command. *)
type 't p_statement = (ident * 't p_arg list * 't) loc

type ('t, 'r) p_command_aux =
  | P_require    of bool * p_module_path list
  (** Require statement (require open if the boolean is true). *)
  | P_require_as of p_module_path * (string * bool) loc
  (** Require as statement. *)
  | P_open       of p_module_path list
  (** Open statement. *)
  | P_symbol     of p_modifier loc list * ident * 't p_arg list * 't
  (** Symbol declaration. *)
  | P_rules      of 'r list
  (** Rewriting rule declarations. *)
  | P_definition of p_modifier loc list * bool * ident * 't p_arg list *
                    't option * 't
  (** Definition of a symbol (unfoldable). *)
  | P_inductive of p_modifier loc list * 't p_inductive list
  (** Definition of inductive type *)
  | P_theorem    of p_modifier loc list * 't p_statement * 't p_tactic list *
                    p_proof_end loc
  (** Theorem with its proof. *)
  | P_set        of 'r p_config
  (** Set the configuration. *)
  | P_query      of 't p_query
  (** Query. *)

(** Parser-level representation of a single (located) command. The first type
    parameter can be instanciated by parser terms of {!module:P_terms s} or
    terms of {!module:Terms}. The second parameter is the type of rewriting
    rules. The two have been separated because a parser level AST has a rule
    type of [(p_term * p_term) loc], but a scoped AST does not have
    [(term * term) loc] rules, but {!type:Scope.pre_rule}. *)
type ('t, 'r) p_command = ('t, 'r) p_command_aux loc

(** Top level AST returned by the parser. *)
type ('t, 'r) ast = ('t, 'r) p_command list

let eq_ident : ident eq = fun x1 x2 -> x1.elt = x2.elt

let eq_qident : qident eq = fun q1 q2 -> q1.elt = q2.elt

let eq_unop : unop eq = fun (n1,p1,id1) (n2,p2,id2) ->
  n1 = n2 && p1 = p2 && eq_qident id1 id2

let eq_binop : binop eq = fun (n1,a1,p1,id1) (n2,a2,p2,id2) ->
  n1 = n2 && a1 = a2 && p1 = p2 && eq_qident id1 id2

(** Equality functions parametrised by terms and equality on terms. *)
module EqAst (T: sig type t val eq : t eq end)
    (R: sig type t val eq : t eq end) = struct

  let eq_p_arg : T.t p_arg eq = fun (x1,ao1,b1) (x2,ao2,b2) ->
    List.equal (Option.equal (fun x1 x2 -> x1.elt = x2.elt)) x1 x2
    && Option.equal T.eq ao1 ao2 && b1 = b2

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

  let eq_p_config : R.t p_config eq = fun c1 c2 ->
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
  let eq_p_command : (T.t, R.t) p_command eq = fun c1 c2 ->
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
        List.equal R.eq rs1 rs2
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

(** Map functions on the first parameter of commands (the terms). *)

(** [p_rw_patt_map f rw_patt] maps function [f] on terms of [rw_patt]. *)
let p_rw_patt_map : 'a 'b. ('a -> 'b) -> 'a p_rw_patt -> 'b p_rw_patt =
  fun f rw_patt ->
  match rw_patt with
  | P_rw_Term(t)                    -> P_rw_Term(f t)
  | P_rw_InTerm(t)                  -> P_rw_InTerm(f t)
  | P_rw_InIdInTerm(id, t)          -> P_rw_InIdInTerm(id, f t)
  | P_rw_IdInTerm(id, t)            -> P_rw_IdInTerm(id, f t)
  | P_rw_TermInIdInTerm(t1, id, t2) -> P_rw_TermInIdInTerm(f t1, id, f t2)
  | P_rw_TermAsIdInTerm(t1, id, t2) -> P_rw_TermAsIdInTerm(f t1, id, f t2)

(** [p_assertion_map f assertion] maps function [f] on terms of
    [assertion]. *)
let p_assertion_map : 'a 'b. ('a -> 'b) -> 'a p_assertion -> 'b p_assertion =
  fun f assertion ->
  match assertion with
  | P_assert_typing(t1, t2) -> P_assert_typing(f t1, f t2)
  | P_assert_conv(t1, t2)   -> P_assert_conv(f t1, f t2)

(** [p_query_map f query] maps function [f] on terms of [query]. *)
let p_query_map : 'a 'b. ('a -> 'b) -> 'a p_query -> 'b p_query =
  fun f {elt = p_query; pos = loc} ->
  let new_query =
    match p_query with
    | P_query_verbose(n)            -> P_query_verbose(n)
    | P_query_debug(b, s)           -> P_query_debug(b, s)
    | P_query_flag(s, b)            -> P_query_flag(s, b)
    | P_query_assert(b, assertion)  ->
        P_query_assert(b, p_assertion_map f assertion)
    | P_query_infer(t, eval_cfg)    -> P_query_infer(f t, eval_cfg)
    | P_query_normalize(t,eval_cfg) -> P_query_normalize(f t, eval_cfg)
    | P_query_prover(s)             -> P_query_prover(s)
    | P_query_prover_timeout(n)     -> P_query_prover_timeout(n)
  in
  Pos.make loc new_query

(** [p_tactic_map f tactic] maps function [f] on terms of [tactic]. *)
let p_tactic_map : 'a 'b. ('a -> 'b) -> 'a p_tactic -> 'b p_tactic =
  fun f {elt = p_tactic; pos = loc} ->
  let new_tactic =
    match p_tactic with
    | P_tac_refine(t)                       -> P_tac_refine(f t)
    | P_tac_intro(idopt_l)                  -> P_tac_intro(idopt_l)
    | P_tac_apply(t)                        -> P_tac_apply(f t)
    | P_tac_simpl                           -> P_tac_simpl
    | P_tac_rewrite(b, rw_patt_loc_opt, t)  ->
      let map_rw_patt_loc {elt = rw_patt; pos = loc} =
        Pos.make loc (p_rw_patt_map f rw_patt)
      in
      P_tac_rewrite(b, Option.map map_rw_patt_loc rw_patt_loc_opt, f t)
    | P_tac_refl                            -> P_tac_refl
    | P_tac_sym                             -> P_tac_sym
    | P_tac_focus(n)                        -> P_tac_focus(n)
    | P_tac_print                           -> P_tac_print
    | P_tac_proofterm                       -> P_tac_proofterm
    | P_tac_why3(s_opt)                     -> P_tac_why3(s_opt)
    | P_tac_query(query) -> P_tac_query(p_query_map f query)
    | P_tac_fail                            -> P_tac_fail
  in
  Pos.make loc new_tactic

(** [p_config_map f p_config] maps function [f] on terms of [p_config]. *)
let p_config_map : 'a 'b. ('a -> 'b) -> 'a p_config -> 'b p_config =
  fun f p_config ->
  match p_config with
  | P_config_builtin(s, qid)      -> P_config_builtin(s, qid)
  | P_config_unop(unop)           -> P_config_unop(unop)
  | P_config_binop(binop)         -> P_config_binop(binop)
  | P_config_ident(s)             -> P_config_ident(s)
  | P_config_quant(qid)           -> P_config_quant(qid)
  | P_config_unif_rule(r)         -> P_config_unif_rule(f r)


(** [p_cmd_map f cmd] maps function [f] on terms of [cmd]. *)
let p_cmd_map : 'a 'b 'c. ('a -> 'b) -> ('a, 'c) p_command ->
  ('b, 'c) p_command = fun f cmd ->
  let map_arg_list =
    let arg_map : 'a p_arg -> 'b p_arg = fun (sloptl, termopt, b) ->
      (sloptl, Option.map f termopt, b)
    in
    List.map arg_map
  in
  let f e =
    match e with
    | P_require(b, pl) -> P_require(b, pl)
    | P_require_as(pl, sbl) -> P_require_as(pl, sbl)
    | P_open(pl) -> P_open(pl)
    | P_symbol(pl, id, argl, t) -> P_symbol(pl, id, map_arg_list argl, f t)
    | P_rules(rs) -> P_rules(rs)
    | P_definition(pl, b, id, argl, topt, t) ->
      P_definition(pl, b, id, map_arg_list argl, Option.map f topt, f t)
    | P_inductive(ms, is) ->
        let im : 'a p_inductive -> 'b p_inductive =
          fun {elt=(id,t,its); pos} ->
            let t = f t in
            let its = List.map (fun (i,t) -> (i, f t)) its in
            Pos.make pos (id, t, its)
        in
        P_inductive(ms, List.map im is)
    | P_theorem(pl, statement, tactics, proof_end) ->
        let st_map st =
          Pos.map (fun (id, p_arg_l, t) -> (id,map_arg_list p_arg_l, f t)) st
        in
        let tactics   = List.map (p_tactic_map f) tactics in
        P_theorem(pl, st_map statement, tactics, proof_end)
    | P_set(p_config) -> P_set(p_config)
    | P_query(query)  -> P_query(p_query_map f query)
  in
  Pos.map f cmd
