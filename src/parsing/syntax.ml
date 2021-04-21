(** Parser-level abstract syntax. *)

open Lplib
open Lplib.Base
open Lplib.Extra
open Common
open Pos
open Core

(** Representation of a (located) identifier. *)
type p_ident = strloc

(** [notin id idopts] checks that [id] does not occur in [idopts]. *)
let check_notin : string -> p_ident option list -> unit = fun id ->
  let rec notin = function
    | [] -> ()
    | None :: idopts -> notin idopts
    | Some {elt=id';pos} :: idopts ->
        if id' = id then Error.fatal pos "%s already used." id
        else notin idopts
  in notin

(** [are_distinct idopts] checks that the elements of [idopts] of the form
   [Some _] are pairwise distinct. *)
let rec check_distinct : p_ident option list -> unit = function
  | [] -> ()
  | None :: idopts -> check_distinct idopts
  | Some {elt=id;_} :: idopts -> check_notin id idopts; check_distinct idopts

(** Identifier of a metavariable. *)
type meta_ident = Name of string | Numb of int
type p_meta_ident = meta_ident loc

(** Representation of a module name. *)
type p_path = Path.t loc

(** Representation of a possibly qualified (and located) identifier. *)
type qident = Term.qident
type p_qident = qident loc

(** Parser-level (located) term representation. *)
type p_term = p_term_aux loc
and p_term_aux =
  | P_Type (** TYPE constant. *)
  | P_Iden of p_qident * bool (** Identifier. The boolean indicates whether
                                 the identifier is prefixed by "@". *)
  | P_Wild (** Underscore. *)
  | P_Meta of p_meta_ident * p_term array option
    (** Meta-variable application. *)
  | P_Patt of p_ident option * p_term array option (** Pattern. *)
  | P_Appl of p_term * p_term (** Application. *)
  | P_Arro of p_term * p_term (** Arrow. *)
  | P_Abst of p_params list * p_term (** Abstraction. *)
  | P_Prod of p_params list * p_term (** Product. *)
  | P_LLet of p_ident * p_params list * p_term option * p_term * p_term
    (** Let. *)
  | P_NLit of int (** Natural number literal. *)
  | P_Wrap of p_term (** Term between parentheses. *)
  | P_Expl of p_term (** Term between curly brackets. *)

(** Parser-level representation of a function argument. The boolean is true if
    the argument is marked as implicit (i.e., between curly braces). *)
and p_params = p_ident option list * p_term option * bool

(** [nb_params ps] returns the number of parameters in a list of parameters
    [ps]. *)
let nb_params : p_params list -> int =
  List.fold_left (fun acc (ps,_,_) -> acc + List.length ps) 0

(** [get_impl_params_list l] gives the implicitness of [l]. *)
let rec get_impl_params_list : p_params list -> bool list = function
  | [] -> []
  | (params,_,impl)::params_list ->
      List.map (fun _ -> impl) params @ get_impl_params_list params_list

(** [get_impl_term t] gives the implicitness of [t]. *)
let rec get_impl_term : p_term -> bool list = fun t -> get_impl_term_aux t.elt
and get_impl_term_aux : p_term_aux -> bool list = fun t ->
  match t with
  | P_Prod([],t) -> get_impl_term t
  | P_Prod((ys,_,impl)::xs,t) ->
      List.map (fun _ -> impl) ys @ get_impl_term_aux (P_Prod(xs,t))
  | P_Arro(_,t)  -> false :: get_impl_term t
  | P_Wrap(t)    -> get_impl_term t
  | _            -> []

(** [p_get_args t] is {!val:LibTerm.get_args} on syntax-level terms. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args acc t =
    match t.elt with
    | P_Appl(t, u) -> p_get_args (u::acc) t
    | _            -> (t, acc)
  in p_get_args [] t

(** Parser-level rewriting rule representation. *)
type p_rule_aux = p_term * p_term
type p_rule = p_rule_aux loc

(** A coercion [(id, def, dty, k, a, r)] is named [id], defined by term [def]
    of type [dty], coerces on its [k]th argument to provide a term whose type
    is of arity [a]. [r] is a list of required coercions. *)
type p_coercion_aux =
  { p_coer_id : p_ident (** A name for the coercion. *)
  ; p_coer_def : p_term (** Definition of the coercion. *)
  ; p_coer_typ : p_term (** Type of the coercion. *)
  ; p_coer_src : int
  (** Indicate which argument applied to [p_coer_def] is coerced. First
      argument is numbered 1. *)
  ; p_coer_ari : int (** Arity of the type to which the term is coerced. *)
  ; p_coer_req : (p_ident * p_term ) list
  (** A list of required coercions that must be found to apply this one. *) }
type p_coercion = p_coercion_aux loc

(** Parser-level inductive type representation. *)
type p_inductive_aux = p_ident * p_term * (p_ident * p_term) list
type p_inductive = p_inductive_aux loc

(** Module to create p_term's with no positions. *)
module P  = struct

  (** [qiden p s] builds a [P_Iden] "@p.s". *)
  let qiden : Path.t -> string -> p_term = fun p s ->
    Pos.none (P_Iden(Pos.none (p, s), true))

  (** [iden s] builds a [P_Iden] "@s". *)
  let iden : string -> p_term = qiden []

  (** [var v] builds a [P_Iden] from [Bindlib.name_of v]. *)
  let var : Term.tvar -> p_term = fun v -> iden (Bindlib.name_of v)

  (** [patt s ts] builds a [P_Patt] "$s[ts]". *)
  let patt : string -> p_term array option -> p_term = fun s ts ->
    Pos.none (P_Patt (Some (Pos.none s), ts))

  (** [patt0 s] builds a [P_Patt] "$s". *)
  let patt0 : string -> p_term = fun s -> patt s None

  (** [appl t u] builds [P_Appl(t, u)]. *)
  let appl : p_term -> p_term -> p_term = fun t u -> Pos.none (P_Appl(t, u))

  (** [appl_list t ts] iterates [appl]. *)
  let appl_list : p_term -> p_term list -> p_term = List.fold_left appl

  (** [wild] builds a [P_Wild]. *)
  let wild = Pos.none P_Wild

  (** [appl_wild t n] applies [t] to [n] underscores. *)
  let rec appl_wild : p_term -> int -> p_term = fun t i ->
      if i <= 0 then t else appl_wild (appl t wild) (i-1)

  (** [abst idopt t] builds a [P_Abst] over [t]. *)
  let abst : p_ident option -> p_term -> p_term = fun idopt t ->
    Pos.none (P_Abst([[idopt],None,false], t))

  (** [abst_list] iterates [abst]. *)
  let abst_list : p_ident option list -> p_term -> p_term = fun idopts t ->
    List.fold_right abst idopts t

  let rule : p_term -> p_term -> p_rule = fun l r -> Pos.none (l,r)
end

(** Rewrite patterns as in Coq/SSReflect. See "A Small Scale
    Reflection Extension for the Coq system", by Georges Gonthier,
    Assia Mahboubi and Enrico Tassi, INRIA Research Report 6455, 2016,
    @see <http://hal.inria.fr/inria-00258384>, section 8, p. 48. *)
type ('term, 'binder) rw_patt =
  | Rw_Term           of 'term
  | Rw_InTerm         of 'term
  | Rw_InIdInTerm     of 'binder
  | Rw_IdInTerm       of 'binder
  | Rw_TermInIdInTerm of 'term * 'binder
  | Rw_TermAsIdInTerm of 'term * 'binder

type p_rw_patt = (p_term, p_ident * p_term) rw_patt loc

(** Parser-level representation of an assertion. *)
type p_assertion =
  | P_assert_typing of p_term * p_term
  (** The given term should have the given type. *)
  | P_assert_conv   of p_term * p_term
  (** The two given terms should be convertible. *)

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
  | P_query_infer of p_term * Eval.config
  (** Type inference command. *)
  | P_query_normalize of p_term * Eval.config
  (** Normalisation command. *)
  | P_query_prover of string
  (** Set the prover to use inside a proof. *)
  | P_query_prover_timeout of int
  (** Set the timeout of the prover (in seconds). *)
  | P_query_print of p_qident option
  (** Print information about a symbol or the current goals. *)
  | P_query_proofterm
  (** Print the current proof term (possibly containing open goals). *)

type p_query = p_query_aux loc

(** Parser-level representation of a proof tactic. *)
type p_tactic_aux =
  | P_tac_admit
  | P_tac_apply of p_term
  | P_tac_assume of p_ident option list
  | P_tac_fail
  | P_tac_focus of int
  | P_tac_generalize of p_ident
  | P_tac_have of p_ident * p_term
  | P_tac_induction
  | P_tac_query of p_query
  | P_tac_refine of p_term
  | P_tac_refl
  | P_tac_rewrite of bool * p_rw_patt option * p_term
  (* The boolean indicates if the equation is applied from left to right. *)
  | P_tac_simpl of p_qident option
  | P_tac_solve
  | P_tac_sym
  | P_tac_why3 of string option

type p_tactic = p_tactic_aux loc

(** Parser-level representation of a proof terminator. *)
type p_proof_end_aux =
  | P_proof_end
  (** The proof is done and fully checked. *)
  | P_proof_admitted
  (** Give up current state and admit the theorem. *)
  | P_proof_abort
  (** Abort the proof (theorem not admitted). *)

type p_proof_end = p_proof_end_aux loc

(** Parser-level representation of modifiers. *)
type p_modifier_aux =
  | P_mstrat of Term.match_strat (** pattern matching strategy *)
  | P_expo of Term.expo (** visibility of symbol outside its modules *)
  | P_prop of Term.prop (** symbol properties: constant, definable, ... *)
  | P_opaq (** opacity *)

type p_modifier = p_modifier_aux loc

let is_prop {elt; _} = match elt with P_prop(_) -> true | _ -> false
let is_opaq {elt; _} = match elt with P_opaq -> true | _ -> false
let is_expo {elt; _} = match elt with P_expo(_) -> true | _ -> false
let is_mstrat {elt; _} = match elt with P_mstrat(_) -> true | _ -> false

(** Parser-level representation of symbol declarations. *)
type p_symbol =
  { p_sym_mod : p_modifier list (** modifiers *)
  ; p_sym_nam : p_ident (** symbol name *)
  ; p_sym_arg : p_params list (** arguments before ":" *)
  ; p_sym_typ : p_term option (** symbol type *)
  ; p_sym_trm : p_term option (** symbol definition *)
  ; p_sym_prf : (p_tactic list * p_proof_end) option (** proof script *)
  ; p_sym_def : bool (** is it a definition ? *) }

(** Parser-level representation of a single command. *)
type p_command_aux =
  | P_require  of bool * p_path list
    (* "require open" if the boolean is true *)
  | P_require_as of p_path * p_ident
  | P_open of p_path list
  | P_symbol of p_symbol
  | P_rules of p_rule list
  | P_inductive of p_modifier list * p_params list * p_inductive list
  | P_builtin of string * p_qident
  | P_notation of p_qident * Sign.notation
  | P_unif_rule of p_rule
  | P_coercion of p_coercion
  | P_query of p_query

(** Parser-level representation of a single (located) command. *)
type p_command = p_command_aux loc

(** Top level AST returned by the parser. *)
type ast = p_command Stream.t

(** Equality functions on the syntactic expressions ignoring positions. *)

let eq_p_ident : p_ident eq = fun i1 i2 -> i1.elt = i2.elt

let eq_p_meta_ident : p_meta_ident eq = fun i1 i2 -> i1.elt = i2.elt

let eq_p_qident : p_qident eq = fun q1 q2 -> q1.elt = q2.elt

let eq_p_path : p_path eq = fun m1 m2 -> m1.elt = m2.elt

let rec eq_p_term : p_term eq = fun {elt=t1;_} {elt=t2;_} ->
  match t1, t2 with
  | P_Type, P_Type
  | P_Wild, P_Wild -> true
  | P_Iden(q1,b1), P_Iden(q2,b2) -> eq_p_qident q1 q2 && b1 = b2
  | P_Meta(i1,ts1), P_Meta(i2,ts2) ->
      eq_p_meta_ident i1 i2 && Option.equal (Array.equal eq_p_term) ts1 ts2
  | P_Patt(io1,ts1), P_Patt(io2,ts2) ->
      Option.equal eq_p_ident io1 io2
      && Option.equal (Array.equal eq_p_term) ts1 ts2
  | P_Appl(t1,u1), P_Appl(t2,u2)
  | P_Arro(t1,u1), P_Arro(t2,u2) -> eq_p_term t1 t2 && eq_p_term u1 u2
  | P_Abst(xs1,t1), P_Abst(xs2,t2)
  | P_Prod(xs1,t1), P_Prod(xs2,t2) ->
      List.equal eq_p_params xs1 xs2 && eq_p_term t1 t2
  | P_LLet(i1,xs1,a1,t1,u1), P_LLet(i2,xs2,a2,t2,u2) ->
      eq_p_ident i1 i2 && List.equal eq_p_params xs1 xs2
      && Option.equal eq_p_term a1 a2 && eq_p_term t1 t2 && eq_p_term u1 u2
  | P_Wrap t1, P_Wrap t2
  | P_Expl t1, P_Expl t2 -> eq_p_term t1 t2
  | P_NLit n1, P_NLit n2 -> n1 = n2
  | _,_ -> false

and eq_p_params : p_params eq = fun (i1,ao1,b1) (i2,ao2,b2) ->
  List.equal (Option.equal eq_p_ident) i1 i2
  && Option.equal eq_p_term ao1 ao2 && b1 = b2

let eq_p_rule : p_rule eq = fun {elt=(l1,r1);_} {elt=(l2,r2);_} ->
  eq_p_term l1 l2 && eq_p_term r1 r2

let eq_p_inductive : p_inductive eq =
  let eq_cons (i1,t1) (i2,t2) = eq_p_ident i1 i2 && eq_p_term t1 t2 in
  fun {elt=(i1,t1,l1);_} {elt=(i2,t2,l2);_} ->
  List.equal eq_cons ((i1,t1)::l1) ((i2,t2)::l2)

let eq_p_rw_patt : p_rw_patt eq = fun {elt=r1;_} {elt=r2;_} ->
  match r1, r2 with
  | Rw_Term t1, Rw_Term t2
  | Rw_InTerm t1, Rw_InTerm t2 -> eq_p_term t1 t2
  | Rw_InIdInTerm(i1,t1), Rw_InIdInTerm(i2,t2)
  | Rw_IdInTerm(i1,t1), Rw_IdInTerm(i2,t2) ->
      eq_p_ident i1 i2 && eq_p_term t1 t2
  | Rw_TermInIdInTerm(t1,(i1,u1)), Rw_TermInIdInTerm(t2,(i2,u2))
  | Rw_TermAsIdInTerm(t1,(i1,u1)), Rw_TermAsIdInTerm(t2,(i2,u2)) ->
      eq_p_term t1 t2 && eq_p_ident i1 i2 && eq_p_term u1 u2
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
  | P_query_print io1, P_query_print(io2) -> Option.equal eq_p_qident io1 io2
  | P_query_verbose n1, P_query_verbose n2 -> n1 = n2
  | P_query_debug (b1,s1), P_query_debug (b2,s2) -> b1 = b2 && s1 = s2
  | P_query_proofterm, P_query_proofterm -> true
  | _, _ -> false

let eq_p_tactic : p_tactic eq = fun {elt=t1;_} {elt=t2;_} ->
  match t1, t2 with
  | P_tac_apply t1, P_tac_apply t2
  | P_tac_refine t1, P_tac_refine t2 -> eq_p_term t1 t2
  | P_tac_have(i1,t1), P_tac_have(i2,t2) ->
      eq_p_ident i1 i2 && eq_p_term t1 t2
  | P_tac_assume xs1, P_tac_assume xs2 ->
      List.equal (Option.equal eq_p_ident) xs1 xs2
  | P_tac_rewrite(b1,p1,t1), P_tac_rewrite(b2,p2,t2) ->
      b1 = b2 && Option.equal eq_p_rw_patt p1 p2 && eq_p_term t1 t2
  | P_tac_query q1, P_tac_query q2 -> eq_p_query q1 q2
  | P_tac_why3 so1, P_tac_why3 so2 -> so1 = so2
  | P_tac_focus n1, P_tac_focus n2 -> n1 = n2
  | P_tac_simpl q1, P_tac_simpl q2 -> Option.equal eq_p_qident q1 q2
  | P_tac_generalize i1, P_tac_generalize i2 -> eq_p_ident i1 i2
  | P_tac_admit, P_tac_admit
  | P_tac_induction, P_tac_induction
  | P_tac_solve, P_tac_solve
  | P_tac_fail, P_tac_fail
  | P_tac_refl, P_tac_refl
  | P_tac_sym, P_tac_sym -> true
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
  && eq_p_ident p_sym_nam1 p_sym_nam2
  && List.equal eq_p_params p_sym_arg1 p_sym_arg2
  && Option.equal eq_p_term p_sym_typ1 p_sym_typ2
  && Option.equal eq_p_term p_sym_trm1 p_sym_trm2
  && Option.equal eq_tac p_sym_prf1 p_sym_prf2
  && p_sym_def1 = p_sym_def2

(** [eq_command c1 c2] tells whether [c1] and [c2] are the same commands. They
    are compared up to source code positions. *)
let eq_p_command : p_command eq = fun {elt=c1;_} {elt=c2;_} ->
  match c1, c2 with
  | P_require(b1,l1), P_require(b2,l2) ->
      b1 = b2 && List.equal eq_p_path l1 l2
  | P_open l1, P_open l2 -> List.equal eq_p_path l1 l2
  | P_require_as(m1,i1), P_require_as(m2,i2) ->
      eq_p_path m1 m2 && eq_p_ident i1 i2
  | P_symbol s1, P_symbol s2 -> eq_p_symbol s1 s2
  | P_rules(r1), P_rules(r2) ->  List.equal eq_p_rule r1 r2
  | P_inductive(m1,xs1,l1), P_inductive(m2,xs2,l2) ->
      m1 = m2 && List.equal eq_p_params xs1 xs2
      && List.equal eq_p_inductive l1 l2
  | P_builtin(s1,q1), P_builtin(s2,q2) -> s1 = s2 && eq_p_qident q1 q2
  | P_notation(i1,n1), P_notation(i2,n2) -> eq_p_qident i1 i2 && n1 = n2
  | P_unif_rule r1, P_unif_rule r2 -> eq_p_rule r1 r2
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
  assume h
  apply h
  // proof of A->A
  assume a
  apply a // here a is an assumption
  // proof of A
  apply a // here a is a function symbol
end; *)

let fold_idents : ('a -> p_qident -> 'a) -> 'a -> p_command list -> 'a =
  fun f ->

  let add_idopt : StrSet.t -> p_ident option -> StrSet.t = fun vs idopt ->
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
    | P_Arro (t, u) -> fold_term_vars vs (fold_term_vars vs a t) u

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
  in

  let fold_term : 'a -> p_term -> 'a = fold_term_vars StrSet.empty in

  let fold_rule : 'a -> p_rule -> 'a = fun a {elt=(l,r);_} ->
    fold_term (fold_term a l) r
  in

  let fold_rw_patt_vars : StrSet.t -> 'a -> p_rw_patt -> 'a = fun vs a p ->
    match p.elt with
    | Rw_Term t
    | Rw_InTerm t -> fold_term_vars vs a t
    | Rw_InIdInTerm (id, t)
    | Rw_IdInTerm (id, t) -> fold_term_vars (StrSet.add id.elt vs) a t
    | Rw_TermInIdInTerm (t, (id, u))
    | Rw_TermAsIdInTerm (t, (id, u)) ->
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

  let fold_tactic : StrSet.t * 'a -> p_tactic -> StrSet.t * 'a =
    fun (vs,a) t ->
    match t.elt with
    | P_tac_refine t
    | P_tac_apply t
    | P_tac_rewrite (_, None, t) -> (vs, fold_term_vars vs a t)
    | P_tac_rewrite (_, Some p, t) ->
        (vs, fold_term_vars vs (fold_rw_patt_vars vs a p) t)
    | P_tac_query q -> (vs, fold_query_vars vs a q)
    | P_tac_assume idopts -> (add_idopts vs idopts, a)
    | P_tac_have(id,t) -> (StrSet.add id.elt vs, fold_term_vars vs a t)
    | P_tac_simpl (Some qid) -> (vs, f a qid)
    | P_tac_simpl None
    | P_tac_admit
    | P_tac_refl
    | P_tac_sym
    | P_tac_focus _
    | P_tac_why3 _
    | P_tac_solve
    | P_tac_fail
    | P_tac_generalize _
    | P_tac_induction -> (vs, a)
  in

  let fold_inductive_vars : StrSet.t -> 'a -> p_inductive -> 'a =
    fun vs a {elt = (id,t,cons_list); _} ->
    let fold_cons a (_,t) = fold_term_vars vs a t in
    List.fold_left fold_cons a ((id,t)::cons_list)
  in

  let fold_proof : 'a -> (p_tactic list * p_proof_end) -> 'a =
    fun a (ts, _) -> snd (List.fold_left fold_tactic (StrSet.empty, a) ts)
  in

  let fold_args : StrSet.t * 'a -> p_params -> StrSet.t * 'a =
    fun (vs,a) (idopts, tyopt, _) ->
    add_idopts vs idopts,
    match tyopt with
    | None -> a
    | Some t -> fold_term_vars vs a t
  in

  let fold_command : 'a -> p_command -> 'a = fun a {elt;pos} ->
    match elt with
    | P_require (_, _)
    | P_require_as (_, _)
    | P_open _ -> a
    | P_query q -> fold_query_vars StrSet.empty a q
    | P_builtin (_, qid)
    | P_notation (qid, _) -> f a qid
    | P_unif_rule r -> fold_rule a r
    | P_rules rs -> List.fold_left fold_rule a rs
    | P_coercion _ -> assert false
    | P_inductive (_, xs, ind_list) ->
        let vs, a = List.fold_left fold_args (StrSet.empty, a) xs in
        List.fold_left (fold_inductive_vars vs) a ind_list
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
