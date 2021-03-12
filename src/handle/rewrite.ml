(** Implementation of the rewrite tactic. *)

open! Lplib

open Timed
open Common
open Pos
open Core
open Term
open LibTerm
open Error
open Print
open Proof
open Debug

(** Logging function for the rewrite tactic. *)
let log_rewr = new_logger 'r' "rewr" "the rewrite tactic"
let log_rewr = log_rewr.logger

(** [eq ctx t u] tests the equality of [t] and [u] (up to α-equivalence).
    It fails if [t] or [u] contain terms of the form [Patt(i,s,e)] or
    [TEnv(te,env)].  In the process, subterms of the form [TRef(r)] in [t] and
    [u] may be set with the corresponding value to enforce equality, and
    variables appearing in [ctx] can be unfolded. In other words, [eq t u] can
    be used to implement non-linear matching. When the
    matching feature is used, one should make sure that [TRef] constructors do
    not appear both in [t] and in [u] at the same time. Indeed, the references
    are set naively, without occurrence checking. *)
let eq : ctxt -> term -> term -> bool = fun ctx a b -> a == b ||
  let exception Not_equal in
  let rec eq l =
    match l with
    | []       -> ()
    | (a,b)::l ->
    begin
    if !log_enabled then log_rewr "eq [%a] [%a]" pp_term a pp_term b;
    match (Ctxt.unfold ctx a, Ctxt.unfold ctx b) with
    | (a          , b          ) when a == b -> eq l
    | (Vari(x1)   , Vari(x2)   ) when Bindlib.eq_vars x1 x2 -> eq l
    | (Type       , Type       )
    | (Kind       , Kind       ) -> eq l
    | (Symb(s1)   , Symb(s2)   ) when s1 == s2 -> eq l
    | (Prod(a1,b1), Prod(a2,b2))
    | (Abst(a1,b1), Abst(a2,b2)) -> let (_, b1, b2) = Bindlib.unbind2 b1 b2 in
                                    eq ((a1,a2)::(b1,b2)::l)
    | (LLet(a1,t1,u1), LLet(a2,t2,u2)) ->
        let (_, u1, u2) = Bindlib.unbind2 u1 u2 in
        eq ((a1,a2)::(t1,t2)::(u1,u2)::l)
    | (Appl(t1,u1), Appl(t2,u2)) -> eq ((t1,t2)::(u1,u2)::l)
    | (Meta(m1,e1), Meta(m2,e2)) when m1 == m2 ->
        eq (if e1 == e2 then l else List.add_array2 e1 e2 l)
    | (Wild       , _          )
    | (_          , Wild       ) -> eq l
    | (TRef(r)    , b          ) -> r := Some(b); eq l
    | (a          , TRef(r)    ) -> r := Some(a); eq l
    | (Patt(_,_,_), _          )
    | (_          , Patt(_,_,_))
    | (TEnv(_,_)  , _          )
    | (_          , TEnv(_,_)  ) -> assert false
    | (_          , _          ) -> raise Not_equal
    end
  in
  try eq [(a,b)]; true with Not_equal -> false

(** Equality configuration. *)
type eq_config =
  { symb_P     : sym (** Encoding of propositions.        *)
  ; symb_T     : sym (** Encoding of types.               *)
  ; symb_eq    : sym (** Equality proposition.            *)
  ; symb_eqind : sym (** Induction principle on equality. *)
  ; symb_refl  : sym (** Reflexivity of equality.         *) }

(** [get_eq_config ss pos] returns the current configuration for
    equality, used by tactics such as “rewrite” or “reflexivity”. *)
let get_eq_config : Sig_state.t -> popt -> eq_config = fun ss pos ->
  let builtin = Builtin.get ss pos in
  { symb_P     = builtin "P"
  ; symb_T     = builtin "T"
  ; symb_eq    = builtin "eq"
  ; symb_eqind = builtin "eqind"
  ; symb_refl  = builtin "refl" }

(* Register checks for the builtin symbols related to rewriting. *)
let _ =
  let check_t_or_p _ss pos sym =
    let valid =
      match Eval.whnf [] !(sym.sym_type) with
      | Prod(_, b) -> Eval.eq_modulo [] (snd (Bindlib.unbind b)) Type
      | _          -> false
    in
    if not valid then
      fatal pos "The type of [%s] is not of the form [_ → TYPE]." sym.sym_name
  in
  (* The type of the builtin ["T"] should be [U → TYPE]. *)
  Builtin.register "T" check_t_or_p;
  (* The type of the builtin ["P"] should be [Prop → TYPE]. *)
  Builtin.register "P" check_t_or_p;
  let get_domain_of_type s =
    match Eval.whnf [] !(s.sym_type) with
    | Prod(a,_) -> a
    | _         -> assert false
  in
  let register_builtin =
    Builtin.register_expected_type (Eval.eq_modulo []) pp_term
  in
  let expected_eq_type pos map =
    (* [Π (a:U), T a → T a → Prop] *)
    let symb_T = Builtin.get pos map "T" in
    let symb_P = Builtin.get pos map "P" in
    let term_U = lift (get_domain_of_type symb_T) in
    let term_Prop = lift (get_domain_of_type symb_P) in
    let a = Bindlib.new_var mkfree "a" in
    let term_T_a = _Appl (_Symb symb_T) (_Vari a) in
    let impls = _Impl term_T_a (_Impl term_T_a term_Prop) in
    Bindlib.unbox (_Prod term_U (Bindlib.bind_var a impls))
  in
  register_builtin "eq" expected_eq_type;
  let expected_refl_type pos map =
    (* [Π (a:U) (x:T a), P (eq a x x)] *)
    let symb_T = Builtin.get pos map "T" in
    let symb_P = Builtin.get pos map "P" in
    let symb_eq = Builtin.get pos map "eq" in
    let term_U = lift (get_domain_of_type symb_T) in
    let a = Bindlib.new_var mkfree "a" in
    let x = Bindlib.new_var mkfree "x" in
    let appl_eq = _Appl (_Symb symb_eq) (_Vari a) in
    let appl_eq = _Appl (_Appl appl_eq (_Vari x)) (_Vari x) in
    let appl = _Appl (_Symb symb_P) appl_eq in
    let term_T_a = _Appl (_Symb symb_T) (_Vari a) in
    let prod = _Prod term_T_a (Bindlib.bind_var x appl) in
    Bindlib.unbox (_Prod term_U (Bindlib.bind_var a prod))
  in
  register_builtin "refl" expected_refl_type;
  let expected_eqind_type pos map =
    (* [Π (a:U) (x y:T a), P (eq x y) → Π (p:T a→Prop), P (p y) → P (p x)] *)
    let symb_T = Builtin.get pos map "T" in
    let term_T = _Symb symb_T in
    let symb_P = Builtin.get pos map "P" in
    let term_P = _Symb symb_P in
    let symb_eq = Builtin.get pos map "eq" in
    let term_eq = _Symb symb_eq in
    let term_U = lift (get_domain_of_type symb_T) in
    let term_Prop = lift (get_domain_of_type symb_P) in
    let a = Bindlib.new_var mkfree "a" in
    let x = Bindlib.new_var mkfree "x" in
    let y = Bindlib.new_var mkfree "y" in
    let p = Bindlib.new_var mkfree "p" in
    let term_T_a = _Appl term_T (_Vari a) in
    let term_P_p_x = _Appl term_P (_Appl (_Vari p) (_Vari x)) in
    let term_P_p_y = _Appl term_P (_Appl (_Vari p) (_Vari y)) in
    let impl = _Impl term_P_p_y term_P_p_x in
    let prod = _Prod (_Impl term_T_a term_Prop) (Bindlib.bind_var p impl) in
    let eq = _Appl (_Appl (_Appl term_eq (_Vari a)) (_Vari x)) (_Vari y) in
    let impl = _Impl (_Appl term_P eq) prod in
    let prod = _Prod term_T_a (Bindlib.bind_var y impl) in
    let prod = _Prod term_T_a (Bindlib.bind_var x prod) in
    Bindlib.unbox (_Prod term_U (Bindlib.bind_var a prod))
  in
  register_builtin "eqind" expected_eqind_type

(** [get_eq_data pos cfg a] extra data from an equality type [a]. It
   consists of a triple containing the type in which equality is used and the
   equated terms (LHS and RHS). *)
let get_eq_data : popt -> eq_config -> term -> term * term * term =
  fun pos cfg t ->
  let t = Eval.whnf [] t in
  match LibTerm.get_args t with
  | (p, [u]) when is_symb cfg.symb_P p ->
      begin
        let u = Eval.whnf [] u in
        match LibTerm.get_args u with
        | (eq, [a;l;r]) when is_symb cfg.symb_eq eq -> (a, l, r)
        | _ ->
           fatal pos "Expected an equality type, found [%a]." pp_term t
      end
  | _ -> fatal pos "Expected an equality type, found [%a]." pp_term t

(** Type of a term with the free variables that need to be substituted (during
    some unification process).  It is usually used to store the LHS of a proof
    of equality, together with the variables that were quantified over. *)
type to_subst = tvar array * term

(** [add_refs t] substitutes each wildcard of [t] using a fresh reference cell
    ([TRef] constructor). This is used for unification, by performing  all the
    substitutions in-place. *)
let rec add_refs : term -> term = fun t ->
  match unfold t with
  | Wild        -> TRef(ref None)
  | Appl(t1,t2) -> Appl(add_refs t1, add_refs t2)
  | _           -> t

(** [break_prod a] eliminates the products at the surface of [a],  and returns
    the remaining term the variables that used to correspond to the eliminated
    products. These variables may appear free in the returned term. *)
let break_prod : term -> term * tvar array = fun a ->
  let rec aux : term -> tvar list -> term * tvar array = fun a vs ->
    match Eval.whnf [] a with
    | Prod(_,b) -> let (v,b) = Bindlib.unbind b in aux b (v::vs)
    | a         -> (a, Array.of_list (List.rev vs))
  in aux a []

(** [match_pattern (xs,p) t] attempts to match the pattern [p] (containing the
    “pattern variables” of [xs]) with the term [t]. If successful,  it returns
    [Some(ts)] where [ts] is an array of terms such that substituting elements
    of [xs] by the corresponding elements of [ts] in [p] yields a term that is
    equal to [t] (in terms of [eq]). *)
let match_pattern : to_subst -> term -> term array option = fun (xs,p) t ->
  let ts = Array.map (fun _ -> TRef(ref None)) xs in
  let p = Bindlib.msubst (Bindlib.unbox (Bindlib.bind_mvar xs (lift p))) ts in
  if eq [] p t then Some(Array.map unfold ts) else None

(** [find_subst t (xs,p)] is given a term [t] and a pattern [p] (with “pattern
    variables” of [xs]),  and it finds the first instance of (a term matching)
    [p] in [t] (if there is any). If successful, the function returns an array
    of terms corresponding to the substitution (see [match_pattern]). *)
let find_subst : term -> to_subst -> term array option = fun t (xs,p) ->
  let time = Time.save () in
  let rec find_sub_aux : term -> term array option = fun t ->
    match match_pattern (xs,p) t with
    | None ->
        begin
          Time.restore time;
          match unfold t with
            | Appl(t,u) ->
                begin
                  match find_sub_aux t with
                  | None -> Time.restore time; find_sub_aux u
                  | sub  -> sub
                end
            | _         -> None
        end
    | sub  -> sub
  in find_sub_aux t

(** [make_pat t p] is given a term [t], and a pattern [p] containing reference
    cells (that are not instantiated) and wildcards.  It then tries to find  a
    subterm of [t] that matches [p], using (instantiating) syntactic equality.
    In case of success, the function returns [true],  and the matching term is
    [p] itself (through instantiation). *)
let make_pat : term -> term -> bool = fun t p ->
  let time = Time.save () in
  let rec make_pat_aux : term -> bool = fun t ->
    if eq [] t p then true else
      begin
        Time.restore time;
        match unfold t with
        | Appl(t,u) ->
            begin
              match make_pat_aux t with
              | false -> Time.restore time; make_pat_aux u
              | true  -> true
            end
        | _         -> false
      end
  in make_pat_aux t

(** [bind_match p t] binds every occurence of the pattern [p] in the term [t].
    We require [t] not to contain products, abstractions, metavariables or any
    other awkward term constructor. *)
let bind_match : term -> term -> tbinder =  fun p t ->
  let x = Bindlib.new_var mkfree "X" in
  let rec lift_subst : term -> tbox = fun t ->
    if eq [] p t then _Vari x else
    match unfold t with
    | Vari(y)     -> _Vari y
    | Type        -> _Type
    | Kind        -> _Kind
    | Symb(s)     -> _Symb s
    | Appl(t,u)   -> _Appl (lift_subst t) (lift_subst u)
    (* For now, we fail on products, abstractions, metavariables and let. *)
    | Prod(_)     -> fatal None "Cannot rewrite under products."
    | Abst(_)     -> fatal None "Cannot rewrite under abstractions."
    | Meta(_)     -> fatal None "Cannot rewrite metavariables."
    | LLet(_)     -> fatal None "Cannot rewrite in let."
    (* Forbidden cases. *)
    | Patt(_,_,_) -> assert false
    | TEnv(_,_)   -> assert false
    | Wild        -> assert false
    | TRef(_)     -> assert false
  in
  Bindlib.(unbox (bind_var x (lift_subst t)))

(* NOTE in [bind_match] we lift while matching for efficiency. *)

(** [swap cfg a r l t] returns a term of type [P (eq a l r)] from a term [t]
   of type [P (eq a r l)]. *)
let swap : eq_config -> term -> term -> term -> term -> term =
  fun cfg a r l t ->
  (* We build the predicate “λx:T a, eq a l x”. *)
  let pred =
    let x = Bindlib.new_var mkfree "x" in
    let pred = add_args (Symb cfg.symb_eq) [a; l; Vari(x)] in
    let pred = Bindlib.unbox (Bindlib.bind_var x (lift pred)) in
    Abst(Appl(Symb cfg.symb_T, a), pred)
  in
  (* We build the proof term. *)
  let refl_a_l = add_args (Symb cfg.symb_refl) [a; l] in
  add_args (Symb cfg.symb_eqind) [a; r; l; t; pred; refl_a_l]

(** [rewrite gt b po t] generates a term for the refine tactic representing
   the application of the rewrite tactic to the goal type [gt]. Every
   occurrence of the first instance of the left-hand side is replaced by the
   right-hand side of the obtained proof (or the reverse if b is false). It
   handles the full set of SSReflect patterns. *)
let rewrite : Sig_state.t -> popt -> goal_typ -> bool -> rw_patt option
              -> term -> term =
  fun ss pos {goal_hyps=g_env; goal_type=g_type; _} l2r p t ->

  (* Obtain the required symbols from the current signature. *)
  let cfg = get_eq_config ss pos in

  (* Infer the type of [t] (the argument given to the tactic). *)
  let g_ctxt = Env.to_ctxt g_env in
  let module Infer = (val Stdlib.(!Refiner.default)) in
  let _, t_type = Infer.infer Unif.solve_noexn ?pos g_ctxt t in

  (* Check that the type of [t] is of the form “P (eq a l r)”. *)
  let (t_type, vars) = break_prod t_type in
  let (a, l, r)  = get_eq_data pos cfg t_type in

  (* Reverse the members of the equation if l2r is false. *)
  let (t, l, r) = if l2r then (t, l, r) else (swap cfg a l r t, r, l) in

  (* Apply [t] to the variables of [vars] to get a witness of the equality. *)
  let t_args = Array.fold_left (fun t x -> Appl(t, Vari(x))) t vars in

  (* Bind the variables in this new witness. *)
  let bound =
    let triple = Bindlib.box_triple (lift t_args) (lift l) (lift r) in
    Bindlib.unbox (Bindlib.bind_mvar vars triple)
  in

  (* Extract the term from the goal type (get “t” from “P t”). *)
  let g_term =
    match LibTerm.get_args g_type with
    | (p, [t]) when is_symb cfg.symb_P p -> t
    | _                                        ->
        fatal pos "Goal type [%a] is not of the form “P t”." pp_term g_type
  in

  (* Obtain the different components depending on the pattern. *)
  let (pred_bind, new_term, t, l, r) =
    match p with
    (* Simple rewrite, no pattern. *)
    | None                         ->
        (* Build a substitution from the first instance of [l] in the goal. *)
        let sigma =
          match find_subst g_term (vars, l) with
          | Some(sigma) -> sigma
          | None        ->
              fatal pos "No subterm of [%a] matches [%a]."
                pp_term g_term pp_term l
        in
        (* Build the required data from that substitution. *)
        let (t, l, r) = Bindlib.msubst bound sigma in
        let pred_bind = bind_match l g_term in
        (pred_bind, Bindlib.subst pred_bind r, t, l, r)

    (* Basic patterns. *)
    | Some(RW_Term(p)            ) ->
        (* Find a subterm [match_p] of the goal that matches [p]. *)
        let match_p =
          let p_refs = add_refs p in
          if not (make_pat g_term p_refs) then
            fatal pos "No subterm of [%a] matches [%a]."
              pp_term g_term pp_term p;
          p_refs (* [TRef] cells have been instantiated here. *)
        in
        (* Build a substitution by matching [match_p] with the LHS [l]. *)
        let sigma =
          match match_pattern (vars,l) match_p with
          | Some(sigma) -> sigma
          | None        ->
              fatal pos "No subterm of [%a] matches [%a]."
                pp_term match_p pp_term l
        in
        (* Build the data from the substitution. *)
        let (t, l, r) = Bindlib.msubst bound sigma in
        let pred_bind = bind_match l g_term in
        (pred_bind, Bindlib.subst pred_bind r, t, l, r)

    (* Nested patterns. *)
    | Some(RW_InTerm(p)          ) ->
        (* Find a subterm [match_p] of the goal that matches [p]. *)
        let match_p =
          let p_refs = add_refs p in
          if not (make_pat g_term p_refs) then
            fatal pos "No subterm of [%a] matches [%a]."
              pp_term g_term pp_term p;
          p_refs (* [TRef] cells have been instantiated here. *)
        in
        (* Build a substitution from a subterm of [match_p] matching [l]. *)
        let sigma =
          match find_subst match_p (vars,l) with
          | Some(sigma) -> sigma
          | None        ->
              fatal pos "No subterm of the pattern [%a] matches [%a]."
                pp_term match_p pp_term l
        in
        (* Build the data from the substitution. *)
        let (t, l, r) = Bindlib.msubst bound sigma in
        let p_x = bind_match l match_p in
        let p_r = Bindlib.subst p_x r in
        let pred_bind = bind_match match_p g_term in
        let new_term = Bindlib.subst pred_bind p_r in
        let (x, p_x) = Bindlib.unbind p_x in
        let pred_box = lift (Bindlib.subst pred_bind p_x) in
        let pred_bind = Bindlib.unbox (Bindlib.bind_var x pred_box) in
        (pred_bind, new_term, t, l, r)

    | Some(RW_IdInTerm(p)        ) ->
        (* The code here works as follows: *)
        (* 1 - Try to match [p] with some subterm of the goal. *)
        (* 2 - If we succeed we do two things, we first replace [id] with its
               value, [id_val], the value matched to get [pat_l] and  try to
               match [id_val] with the LHS of the lemma. *)
        (* 3 - If we succeed we create the "RHS" of the pattern, which is [p]
               with [sigma r] in place of [id]. *)
        (* 4 - We then construct the following binders:
               a - [pred_bind_l] : A binder with a new variable replacing each
                   occurrence of [pat_l] in g_term.
               b - [pred_bind] : A binder with a new variable only replacing
                   the subterms where a rewrite happens. *)
        (* 5 - The new goal [new_term] is constructed by substituting [r_pat]
               in [pred_bind_l]. *)
        let (id,p) = Bindlib.unbind p in
        let p_refs = add_refs p in
        let id_val =
          match find_subst g_term ([|id|],p_refs) with
          | Some(id_val) -> id_val.(0)
          | None         ->
              fatal pos "The pattern [%a] does not match [%a]."
                pp_term p pp_term l
        in
        let pat = Bindlib.unbox (Bindlib.bind_var id (lift p_refs)) in
        (* The LHS of the pattern, i.e. the pattern with id replaced by *)
        (* id_val. *)
        let pat_l = Bindlib.subst pat id_val in

        (* This must match with the LHS of the equality proof we use. *)
        let sigma =
          match match_pattern (vars,l) id_val with
          | Some(sigma) -> sigma
          | None        ->
              fatal pos
                "The value of [%s], [%a], in [%a] does not match [%a]."
                (Bindlib.name_of id) pp_term id_val pp_term p pp_term l
        in
        (* Build t, l, using the substitution we found. Note that r  *)
        (* corresponds to the value we get by applying rewrite to *)
        (* id val. *)
        let (t,l,r) = Bindlib.msubst bound sigma in

        (* The RHS of the pattern, i.e. the pattern with id replaced *)
        (* by the result of rewriting id_val. *)
        let pat_r = Bindlib.subst pat r in

        (* Build the predicate, identifying all occurrences of pat_l *)
        (* substituting them, first with pat_r, for the new goal and *)
        (* then with l_x for the lambda term. *)
        let pred_bind_l = bind_match pat_l g_term in

        (* This will be the new goal. *)
        let new_term = Bindlib.subst pred_bind_l pat_r in

        (* [l_x] is the pattern with [id] replaced by the variable X *)
        (* that we use for building the predicate. *)
        let (x, l_x) = Bindlib.unbind pat in
        let pred_box = lift (Bindlib.subst pred_bind_l l_x) in
        let pred_bind = Bindlib.unbox (Bindlib.bind_var x pred_box) in
        (pred_bind, new_term, t, l, r)

    (* Combinational patterns. *)
    | Some(RW_TermInIdInTerm(s,p)) ->
        (* This pattern combines the previous.  First, we identify the subterm
           of [g_term] that matches with [p] where [p] contains an identifier.
           Once we have the value that the identifier in [p] has been  matched
           to, we find a subterm of it that matches with [s].  Then in all the
           occurrences of the first instance of [p] in [g_term] we rewrite all
           occurrences of the first instance of [s] in the subterm of [p] that
           was matched with the identifier. *)
        let (id,p) = Bindlib.unbind p in
        let p_refs = add_refs p in
        let id_val =
          match find_subst g_term ([|id|],p_refs) with
          | Some(id_val) -> id_val
          | None         ->
              fatal pos "The pattern [%a] does not match [%a]."
                pp_term p pp_term l
        in
        (* Once we get the value of id, we work with that as our main term
           since this is where s will appear and will be substituted in. *)
        let id_val = id_val.(0) in
        (* [pat] is the full value of the pattern, with the wildcards now
           replaced by subterms of the goal and [id]. *)
        let pat = Bindlib.unbox (Bindlib.bind_var id (lift p_refs)) in
        let pat_l = Bindlib.subst pat id_val in

        (* We then try to match the wildcards in [s] with subterms of
           [id_val]. *)
        let s_refs = add_refs s in
        if not (make_pat id_val s_refs) then
          fatal pos "The value of [%s], [%a], in [%a] does not match [%a]."
            (Bindlib.name_of id) pp_term id_val pp_term p pp_term s;
        (* Now we must match s, which no longer contains any TRef's
           with the LHS of the lemma,*)
        let s = s_refs in
        let sigma =
          match match_pattern (vars,l) s with
          | Some(sigma) -> sigma
          | None        ->
              fatal pos "The term [%a] does not match the LHS [%a]"
                pp_term s pp_term l
        in
        let (t,l,r) = Bindlib.msubst bound sigma in

        (* First we work in [id_val], that is, we substitute all
           the occurrences of [l] in [id_val] with [r]. *)
        let id_bind = bind_match l id_val in

        (* [new_id] is the value of [id_val] with [l] replaced
           by [r] and [id_x] is the value of [id_val] with the
           free variable [x]. *)
        let new_id = Bindlib.subst id_bind r in
        let (x, id_x) = Bindlib.unbind id_bind in

        (* Then we replace in pat_l all occurrences of [id]
           with [new_id]. *)
        let pat_r = Bindlib.subst pat new_id in

        (* To get the new goal we replace all occurrences of
          [pat_l] in [g_term] with [pat_r]. *)
        let pred_bind_l = bind_match pat_l g_term in

        (* [new_term] is the type of the new goal meta. *)
        let new_term = Bindlib.subst pred_bind_l pat_r in

        (* Finally we need to build the predicate. First we build
           the term l_x, in a few steps. We substitute all the
           rewrites in new_id with x and we repeat some steps. *)
        let l_x = Bindlib.subst pat id_x in

        (* The last step to build the predicate is to substitute
           [l_x] everywhere we find [pat_l] and bind that x. *)
        let pred = Bindlib.subst pred_bind_l l_x in
        let pred_bind = Bindlib.bind_var x (lift pred) in
        (Bindlib.unbox pred_bind, new_term, t, l, r)

    | Some(RW_TermAsIdInTerm(s,p)) ->
        (* This pattern is essentially a let clause.  We first match the value
           of [pat] with some subterm of the goal, and then rewrite in each of
           the occurences of [id]. *)
        let (id,pat) = Bindlib.unbind p in
        let s = add_refs s in
        let p_s = Bindlib.subst p s in
        (* Try to match p[s/id] with a subterm of the goal. *)
        let p_refs = add_refs p_s in
        if not (make_pat g_term p_refs) then
            fatal pos "No subterm of [%a] matches the pattern [%a]"
              pp_term g_term pp_term p_s;
        let p = p_refs in
        let pat_refs = add_refs pat in
        (* Here we have already asserted tat an instance of p[s/id] exists
           so we know that this will match something. The step is repeated
           in order to get the value of [id]. *)
        let sub =
          match match_pattern ([|id|], pat_refs) p with
          | Some(sub) -> sub
          | None      -> assert false
        in
        let id_val = sub.(0) in
        (* This part of the term-building is similar to the previous
           case, as we are essentially rebuilding a term, with some
           subterms that are replaced by new ones. *)
        let sigma =
          match match_pattern (vars, l) id_val with
          | Some(sigma) -> sigma
          | None        ->
              fatal pos
                "The value of X, [%a], does not match the LHS, [%a]"
                pp_term id_val pp_term l
        in
        let (t,l,r) = Bindlib.msubst bound sigma in

        (* Now to do some term building. *)
        let p_x = bind_match l p in
        let p_r = Bindlib.subst p_x r in
        let pred_bind = bind_match p g_term in
        let new_term = Bindlib.subst pred_bind p_r in
        let (x, p_x) = Bindlib.unbind p_x in
        let pred_box = lift (Bindlib.subst pred_bind p_x) in
        let pred_bind = Bindlib.(unbox (bind_var x pred_box)) in
        (pred_bind, new_term, t, l, r)

    | Some(RW_InIdInTerm(p)      ) ->
        (* This is very similar to the [RW_IdInTerm] case. Instead of matching
           [id_val] with [l],  we try to match a subterm of [id_val] with [l],
           and then we rewrite this subterm. As a consequence,  we just change
           the way we construct a [pat_r]. *)
        let (id,p) = Bindlib.unbind p in
        let p_refs = add_refs p in
        let id_val =
          match find_subst g_term ([|id|],p_refs) with
          | Some(id_val) -> id_val
          | None         ->
              fatal pos "The pattern [%a] does not match [%a]."
                pp_term p pp_term g_term
        in
        let id_val = id_val.(0) in
        let pat = Bindlib.unbox (Bindlib.bind_var id (lift p_refs)) in
        let pat_l = Bindlib.subst pat id_val in
        let sigma =
          match find_subst id_val (vars,l) with
          | Some(sigma) -> sigma
          | None        ->
              fatal pos
                "The value of [%s], [%a], in [%a] does not match [%a]."
                (Bindlib.name_of id) pp_term id_val pp_term p pp_term l
        in
        let (t,l,r) = Bindlib.msubst bound sigma in

        (* Rewrite in id. *)
        let id_bind = bind_match l id_val in
        let id_val = Bindlib.subst id_bind r in
        let (x, id_x) = Bindlib.unbind id_bind in

        (* The new RHS of the pattern is obtained by rewriting in [id_val]. *)
        let r_val = Bindlib.subst pat id_val in
        let pred_bind_l = bind_match pat_l g_term in
        let new_term = Bindlib.subst pred_bind_l r_val in
        let l_x = Bindlib.subst pat id_x in
        let pred_box = lift (Bindlib.subst pred_bind_l l_x) in
        let pred_bind = Bindlib.unbox (Bindlib.bind_var x pred_box) in
        (pred_bind, new_term, t, l, r)
  in

  (* Construct the predicate (context). *)
  let pred = Abst(Appl(Symb cfg.symb_T, a), pred_bind) in

  (* Construct the new goal and its type. *)
  let goal_type = Appl(Symb cfg.symb_P, new_term) in
  let goal_term = Meta.make g_ctxt goal_type in

  (* Build the final term produced by the tactic, and check its type. *)
  let eqind = Symb cfg.symb_eqind in
  let term = add_args eqind [a; l; r; t; pred; goal_term] in

  (* Debugging data to the log. *)
  if !log_enabled then
    begin
      log_rewr "Rewriting with:";
      log_rewr "  goal           = [%a]" pp_term g_type;
      log_rewr "  equality proof = [%a]" pp_term t;
      log_rewr "  equality type  = [%a]" pp_term t_type;
      log_rewr "  equality LHS   = [%a]" pp_term l;
      log_rewr "  equality RHS   = [%a]" pp_term r;
      log_rewr "  pred           = [%a]" pp_term pred;
      log_rewr "  new goal       = [%a]" pp_term goal_type;
      log_rewr "  produced term  = [%a]" pp_term term;
    end;

  (* Return the proof-term. *)
  term

(** [reflexivity ss pos gt] generates a term for the refine tactic
   corresponding to the application of reflexivity to the goal type [gt]. *)
let reflexivity : Sig_state.t -> popt -> goal_typ -> term =
  fun ss pos {goal_type;_} ->
  (* Obtain the required symbols from the current signature. *)
  let cfg = get_eq_config ss pos in
  (* Check that the type of [g] is of the form [P (eq a l r)]. *)
  let (a, l, _)  = get_eq_data pos cfg goal_type in
  (* Build the witness. *)
  add_args (Symb cfg.symb_refl) [a; l]

(** [symmetry ss pos gt] generates a term for the refine tactic corresponding
   to the application of symmetry to the goal type [gt], that is, it
   transforms a goal of the form [P (eq a l r)] into [P (eq a r l)]. *)
let symmetry : Sig_state.t -> popt -> goal_typ -> term =
  fun ss pos {goal_hyps; goal_type; _} ->
  (* Obtain the required symbols from the current signature. *)
  let cfg = get_eq_config ss pos in
  (* Check that the type of [g] is of the form “P (eq a l r)”. *)
  let (a, l, r) = get_eq_data pos cfg goal_type in
  (* We create a new metavariable of type [P (eq a r l)]. *)
  let meta_type =
    Appl(Symb cfg.symb_P, (add_args (Symb cfg.symb_eq) [a; r; l])) in
  let meta_term = Meta.make (Env.to_ctxt goal_hyps) meta_type in
  (* NOTE The proofterm is “eqind a r l M (λx,eq a l x) (refl a l)”. *)
  let term = swap cfg a r l meta_term in
  (* Debugging data to the log. *)
  if !log_enabled then
    begin
      log_rewr "Symmetry with:";
      log_rewr "  goal       = [%a]" pp_term goal_type;
      log_rewr "  new goal   = [%a]" pp_term meta_type;
      log_rewr "  proof term = [%a]" pp_term term
    end;
  (* Return the proof-term. *)
  term
