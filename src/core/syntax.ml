(** Parser-level abstract syntax. *)

open Lplib
open Lplib.Base
open Lplib.Extra
open Pos

(** Representation of a (located) identifier. *)
type ident = strloc

(** Parsing representation of a module path. For every path member the boolean
    indicates whether it was given using the escaped syntax. *)
type p_module_path = (string * bool) list

(** Representation of a possibly qualified (and located) identifier. *)
type qident_aux = p_module_path * string
type qident = qident_aux loc

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
type p_rule_aux = p_patt * p_term
type p_rule = p_rule_aux loc

(** Parser-level inductive type representation. *)
type p_inductive_aux = ident * p_args list * p_term * (ident * p_term) list
type p_inductive = p_inductive_aux loc

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
type p_rw_patt_aux =
  | P_rw_Term           of p_term
  | P_rw_InTerm         of p_term
  | P_rw_InIdInTerm     of ident * p_term
  | P_rw_IdInTerm       of ident * p_term
  | P_rw_TermInIdInTerm of p_term * ident * p_term
  | P_rw_TermAsIdInTerm of p_term * ident * p_term
type p_rw_patt = p_rw_patt_aux loc

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
  | P_tac_rewrite of bool * p_rw_patt option * p_term
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
  | P_config_ident of string
  (** Defines a new, valid identifier (e.g., ["σ"], ["€"] or ["ℕ"]). *)
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
type ast = p_command list

(** Equality functions on the syntactic expressions ignoring positions. *)

let eq_ident : ident eq = fun i1 i2 -> i1.elt = i2.elt

let eq_qident : qident eq = fun q1 q2 -> q1.elt = q2.elt

let eq_unop : unop eq = fun (n1,p1,id1) (n2,p2,id2) ->
  n1 = n2 && p1 = p2 && eq_qident id1 id2

let eq_binop : binop eq = fun (n1,a1,p1,id1) (n2,a2,p2,id2) ->
  n1 = n2 && a1 = a2 && p1 = p2 && eq_qident id1 id2

let rec eq_p_term : p_term eq = fun {elt=t1;_} {elt=t2;_} ->
  match t1, t2 with
  | P_Type, P_Type
  | P_Wild, P_Wild -> true
  | P_Iden(q1,b1), P_Iden(q2,b2) -> eq_qident q1 q2 && b1 = b2
  | P_Meta(i1,ts1), P_Meta(i2,ts2) ->
      eq_ident i1 i2 && Option.equal (Array.equal eq_p_term) ts1 ts2
  | P_Patt(io1,ts1), P_Patt(io2,ts2) ->
      Option.equal eq_ident io1 io2
      && Option.equal (Array.equal eq_p_term) ts1 ts2
  | P_Appl(t1,u1), P_Appl(t2,u2)
  | P_Impl(t1,u1), P_Impl(t2,u2) -> eq_p_term t1 t2 && eq_p_term u1 u2
  | P_Abst(xs1,t1), P_Abst(xs2,t2)
  | P_Prod(xs1,t1), P_Prod(xs2,t2) ->
      List.equal eq_p_args xs1 xs2 && eq_p_term t1 t2
  | P_LLet(i1,xs1,a1,t1,u1), P_LLet(i2,xs2,a2,t2,u2) ->
      eq_ident i1 i2 && List.equal eq_p_args xs1 xs2
      && Option.equal eq_p_term a1 a2 && eq_p_term t1 t2 && eq_p_term u1 u2
  | P_UnaO(u1,t1), P_UnaO(u2,t2) -> eq_unop u1 u2 && eq_p_term t1 t2
  | P_BinO(t1,b1,u1), P_BinO(t2,b2,u2) ->
      eq_p_term t1 t2 && eq_binop b1 b2 && eq_p_term u1 u2
  | P_Wrap t1, P_Wrap t2
  | P_Expl t1, P_Expl t2 -> eq_p_term t1 t2
  | P_NLit n1, P_NLit n2 -> n1 = n2
  | _,_ -> false

and eq_p_args : p_args eq = fun (i1,ao1,b1) (i2,ao2,b2) ->
  List.equal (Option.equal eq_ident) i1 i2
  && Option.equal eq_p_term ao1 ao2 && b1 = b2

let eq_p_rule : p_rule eq = fun {elt=(l1,r1);_} {elt=(l2,r2);_} ->
  eq_p_term l1 l2 && eq_p_term r1 r2

let eq_p_inductive : p_inductive eq =
  let eq_cons (i1,t1) (i2,t2) = eq_ident i1 i2 && eq_p_term t1 t2 in
  fun {elt=(i1,xs1,t1,l1);_} {elt=(i2,xs2,t2,l2);_} ->
  List.equal eq_p_args xs1 xs2
  && List.equal eq_cons ((i1,t1)::l1) ((i2,t2)::l2)

let eq_p_rw_patt : p_rw_patt eq = fun {elt=r1;_} {elt=r2;_} ->
  match r1, r2 with
  | P_rw_Term t1, P_rw_Term t2
  | P_rw_InTerm t1, P_rw_InTerm t2 -> eq_p_term t1 t2
  | P_rw_InIdInTerm(i1,t1), P_rw_InIdInTerm(i2,t2)
  | P_rw_IdInTerm(i1,t1), P_rw_IdInTerm(i2,t2) ->
      eq_ident i1 i2 && eq_p_term t1 t2
  | P_rw_TermInIdInTerm(t1,i1,u1), P_rw_TermInIdInTerm(t2,i2,u2)
  | P_rw_TermAsIdInTerm(t1,i1,u1), P_rw_TermAsIdInTerm(t2,i2,u2) ->
      eq_p_term t1 t2 && eq_ident i1 i2 && eq_p_term u1 u2
  | _, _ -> false

let eq_p_assertion : p_assertion eq = fun a1 a2 ->
  match a1, a2 with
  | P_assert_typing(t1,u1), P_assert_typing(t2,u2)
  | P_assert_conv(t1,u1), P_assert_conv(t2,u2) ->
      eq_p_term t1 t2 && eq_p_term u1 u2
  | _, _ -> false

let eq_p_query : p_query eq = fun {elt=q1;_} {elt=q2;_} ->
  match q1, q2 with
  | P_query_assert(b1,a1), P_query_assert(b2,a2) ->
     b1 = b2 && eq_p_assertion a1 a2
  | P_query_infer(t1,c1), P_query_infer(t2,c2)
  | P_query_normalize(t1,c1), P_query_normalize(t2,c2) ->
      eq_p_term t1 t2 && c1 = c2
  | P_query_prover s1, P_query_prover s2 -> s1 = s2
  | P_query_prover_timeout t1, P_query_prover_timeout t2 -> t1 = t2
  | P_query_print io1, P_query_print(io2) -> Option.equal eq_qident io1 io2
  | P_query_verbose n1, P_query_verbose n2 -> n1 = n2
  | P_query_debug (b1,s1), P_query_debug (b2,s2) -> b1 = b2 && s1 = s2
  | P_query_proofterm, P_query_proofterm -> true
  | _, _ -> false

let eq_p_tactic : p_tactic eq = fun {elt=t1;_} {elt=t2;_} ->
  match t1, t2 with
  | P_tac_apply t1, P_tac_apply t2
  | P_tac_refine t1, P_tac_refine t2 -> eq_p_term t1 t2
  | P_tac_intro xs1, P_tac_intro xs2 ->
      List.equal (Option.equal eq_ident) xs1 xs2
  | P_tac_rewrite(b1,p1,t1), P_tac_rewrite(b2,p2,t2) ->
      b1 = b2 && Option.equal eq_p_rw_patt p1 p2 && eq_p_term t1 t2
  | P_tac_query q1, P_tac_query q2 -> eq_p_query q1 q2
  | P_tac_why3 so1, P_tac_why3 so2 -> so1 = so2
  | P_tac_focus n1, P_tac_focus n2 -> n1 = n2
  | P_tac_simpl, P_tac_simpl
  | P_tac_solve, P_tac_solve
  | P_tac_fail, P_tac_fail
  | P_tac_refl, P_tac_refl
  | P_tac_sym, P_tac_sym -> true
  | _, _ -> false

let eq_p_config : p_config eq = fun c1 c2 ->
  match (c1, c2) with
  | P_config_builtin(s1,q1), P_config_builtin(s2,q2) ->
      s1 = s2 && eq_qident q1 q2
  | P_config_unop u1, P_config_unop u2 -> eq_unop u1 u2
  | P_config_binop b1, P_config_binop b2 -> eq_binop b1 b2
  | P_config_quant q1, P_config_quant q2 -> eq_qident q1 q2
  | P_config_unif_rule r1, P_config_unif_rule r2 -> eq_p_rule r1 r2
  | _, _ -> false

let eq_p_symbol : p_symbol eq =
  let eq_tac (ts1,pe1) (ts2,pe2) =
    List.equal eq_p_tactic ts1 ts2 && pe1.elt = pe2.elt in
  fun
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
  && Option.equal eq_tac p_sym_prf1 p_sym_prf2
  && p_sym_def1 = p_sym_def2

(** [eq_command c1 c2] tells whether [c1] and [c2] are the same commands. They
    are compared up to source code positions. *)
let eq_p_command : p_command eq = fun {elt=c1;_} {elt=c2;_} ->
  match c1, c2 with
  | P_require(b1,ps1), P_require(b2,ps2) -> b1 = b2 && List.equal (=) ps1 ps2
  | P_open ps1, P_open ps2 -> List.equal (=) ps1 ps2
  | P_require_as(p1,{elt=(s1,b1);_}),
    P_require_as(p2,{elt=(s2,b2);_}) -> p1 = p2 && s1 = s2 && b1 = b2
  | P_symbol s1, P_symbol s2 -> eq_p_symbol s1 s2
  | P_rules(r1), P_rules(r2) ->  List.equal eq_p_rule r1 r2
  | P_inductive(m1,l1), P_inductive(m2,l2) ->
      m1 = m2 && List.equal eq_p_inductive l1 l2
  | P_set(c1), P_set(c2) -> eq_p_config c1 c2
  | P_query(q1), P_query(q2) -> eq_p_query q1 q2
  | _, _ -> false

(** [fold_idents f a ast] allows to recursively build a value of type ['a]
   starting from [a] and by applying [f] on each identifier occurring in [ast]
   corresponding to a function symbol: variables (term variables or assumption
   names) are excluded.

NOTE: This function is incomplete if an assumption name hides a function
symbol. Example:

symbol A:TYPE;
symbol a:A;
symbol p:((A->A)->A->A)->A :=
begin
  intro h
  apply h
  // proof of A->A
  intro a
  apply a // here a is an assumption
  // proof of A
  apply a // here a is a function symbol
end; *)

let fold_idents : ('a -> qident -> 'a) -> 'a -> ast -> 'a = fun f ->

  let add_idopt : StrSet.t -> ident option -> StrSet.t = fun vs idopt ->
    match idopt with
    | None -> vs
    | Some id -> StrSet.add id.elt vs
  in

  let add_idopts = List.fold_left add_idopt in

  let rec fold_term_vars : StrSet.t -> 'a -> p_term -> 'a =
    fun vs a {elt;pos} ->
    match elt with
    | P_Iden ({elt=(mp,s);_} as qid, _) ->
        if mp = [] && StrSet.mem s vs then a else f a qid

    | P_Type
    | P_Wild
    | P_Meta (_, None)
    | P_Patt (_, None)
    | P_NLit _ -> a

    | P_Meta (_, Some ts)
    | P_Patt (_, Some ts) -> Array.fold_left (fold_term_vars vs) a ts

    | P_Appl (t, u)
    | P_Impl (t, u) -> fold_term_vars vs (fold_term_vars vs a t) u

    | P_Abst ((idopts,Some t,_)::args_list, u)
    | P_Prod ((idopts,Some t,_)::args_list, u) ->
        fold_term_vars (add_idopts vs idopts) (fold_term_vars vs a t)
          (Pos.make pos (P_Abst (args_list, u)))

    | P_Abst ((idopts,None,_)::args_list, u)
    | P_Prod ((idopts,None,_)::args_list, u) ->
        fold_term_vars (add_idopts vs idopts) a
          (Pos.make pos (P_Abst (args_list, u)))

    | P_Abst ([], t)
    | P_Prod ([], t)
    | P_Wrap t
    | P_Expl t -> fold_term_vars vs a t

    | P_LLet (id, (idopts,None,_)::args_list, u, v, w) ->
        fold_term_vars (add_idopts vs idopts) a
          (Pos.make pos (P_LLet (id, args_list, u, v, w)))
    | P_LLet (id, (idopts,Some t,_)::args_list, u, v, w) ->
        fold_term_vars (add_idopts vs idopts) (fold_term_vars vs a t)
          (Pos.make pos (P_LLet (id, args_list, u, v, w)))

    | P_LLet (id, [], None, v, w) ->
        fold_term_vars (StrSet.add id.elt vs) (fold_term_vars vs a v) w
    | P_LLet (id, [], Some u, v, w) ->
        fold_term_vars (StrSet.add id.elt vs)
          (fold_term_vars vs (fold_term_vars vs a u) v) w

    | P_UnaO (_, _)
    | P_BinO (_, _, _) -> a (*FIXME*)
  in

  let fold_term : 'a -> p_term -> 'a = fold_term_vars StrSet.empty in

  let fold_rule : 'a -> p_rule -> 'a = fun a {elt=(l,r);_} ->
    fold_term (fold_term a l) r
  in

  let fold_rw_patt_vars : StrSet.t -> 'a -> p_rw_patt -> 'a = fun vs a p ->
    match p.elt with
    | P_rw_Term t
    | P_rw_InTerm t -> fold_term_vars vs a t
    | P_rw_InIdInTerm (id, t)
    | P_rw_IdInTerm (id, t) -> fold_term_vars (StrSet.add id.elt vs) a t
    | P_rw_TermInIdInTerm (t, id, u)
    | P_rw_TermAsIdInTerm (t, id, u) ->
        fold_term_vars (StrSet.add id.elt vs) (fold_term_vars vs a t) u
  in

  let fold_query_vars : StrSet.t -> 'a -> p_query -> 'a = fun vs a q ->
    match q.elt with
    | P_query_verbose _
    | P_query_debug (_, _)
    | P_query_flag (_, _)
    | P_query_prover _
    | P_query_prover_timeout _
    | P_query_print None
    | P_query_proofterm -> a
    | P_query_assert (_, P_assert_typing(t,u))
    | P_query_assert (_, P_assert_conv(t,u)) ->
        fold_term_vars vs (fold_term_vars vs a t) u
    | P_query_infer (t, _)
    | P_query_normalize (t, _) -> fold_term_vars vs a t
    | P_query_print (Some qid) -> f a qid
  in

  let fold_config : 'a -> p_config -> 'a = fun a c ->
    match c with
    | P_config_builtin (_, qid)
    | P_config_unop (_, _, qid)
    | P_config_binop (_, _, _, qid)
    | P_config_quant qid -> f a qid
    | P_config_ident _ -> a
    | P_config_unif_rule r -> fold_rule a r
  in

  let fold_tactic : StrSet.t * 'a -> p_tactic -> StrSet.t * 'a =
    fun (vs,a) t ->
    match t.elt with
    | P_tac_refine t
    | P_tac_apply t
    | P_tac_rewrite (_, None, t) -> (vs, fold_term_vars vs a t)
    | P_tac_rewrite (_, Some p, t) ->
        (vs, fold_term_vars vs (fold_rw_patt_vars vs a p) t)
    | P_tac_query q -> (vs, fold_query_vars vs a q)
    | P_tac_intro idopts -> (add_idopts vs idopts, a)
    | P_tac_simpl
    | P_tac_refl
    | P_tac_sym
    | P_tac_focus _
    | P_tac_why3 _
    | P_tac_solve
    | P_tac_fail -> (vs, a)
  in

  let fold_inductive : 'a -> p_inductive -> 'a =
    fun a {elt = (id,xs,t,cons_list); pos} ->
    let fold_cons a (_,t) = fold_term a (Pos.make pos (P_Prod(xs,t))) in
    List.fold_left fold_cons a ((id,t)::cons_list)
  in

  let fold_proof : 'a -> (p_tactic list * p_proof_end) -> 'a =
    fun a (ts, _) -> snd (List.fold_left fold_tactic (StrSet.empty, a) ts)
  in

  let fold_command : 'a -> p_command -> 'a = fun a {elt;pos} ->
    match elt with
    | P_require (_, _)
    | P_require_as (_, _)
    | P_open _ -> a
    | P_query q -> fold_query_vars StrSet.empty a q
    | P_set c -> fold_config a c
    | P_rules rs -> List.fold_left fold_rule a rs
    | P_inductive (_, ind_list) -> List.fold_left fold_inductive a ind_list
    | P_symbol {p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf;_} ->
        let d = Pos.none P_Type in
        let t = match p_sym_trm with Some t -> t | None -> d in
        Option.fold fold_proof
          (fold_term a
             (Pos.make pos
                (P_LLet (p_sym_nam, p_sym_arg, p_sym_typ, t, d))))
        p_sym_prf
  in

  List.fold_left fold_command
