(** Generating constraints for type inference and type checking. *)

open Timed
open Console
open Terms
open Env
open Print

(** Logging function for typing. *)
let log_infr = new_logger 'i' "infr" "type inference/checking"
let log_infr = log_infr.logger

(** [destruct_prod n prod] returns a tuple [(env, a)] where [a] is constructed - @PROBLEM
    from the term [prod] by destructing (i.e., by unbinding with the [Bindlib]
    terminology) a total [n] dependent products. The free variables created by
    the process are are given (with their types) in the environment [env]. The
    function raises [Invalid_argument] if [prod] does not evaluate to a series
    of (at least) [n] product types. Intuitively, if the term [prod] is of the
    form [∀ (x1:a1) ⋯ (xn:an), a] then the function (roughly) returns [a],
    and the environment [(xn, an) ;⋯; (x1, a1)]. *)
let destruct_prod : int -> term -> env * term = fun n t ->
  let rec build_env i env t =
    if i >= n then (env, t) else
    match Eval.whnf [] t with
    | Prod(a,b) ->
        let (x, b) = Bindlib.unbind b in
        build_env (i+1) (add x (lift (Eval.simplify [] a)) None env) b
    | _         -> invalid_arg "destruct_prod"
  in
  build_env 0 [] t

(** Given a metavariable [m] of arity [n] and type [∀x1:A1,⋯,∀xn:An,B] (with
   [B] being a sort normally), [extend_meta_type m] returns
   [m[x1,⋯,xn],(∀y:p,q),bp,bq] where p=m1[x1,⋯,xn], q=m2[x1,⋯,xn,y], bp is
   a mbinder of [x1,⋯,xn] over p, and bq is a mbinder of [x1,⋯,xn] over q,
   where [y] is a fresh variable, and [m1] and [m2] are fresh metavariables of
   arity [n] and [n+1], and type [∀x1:A1,⋯,∀xn:An,TYPE] and
   [∀x1:A1,⋯,∀xn:An,∀y:m1[x1,⋯,xn],B] respectively. *)
let extend_meta_type : meta -> term * term *
    tmbinder * (term, tbinder) Bindlib.mbinder = fun m ->
  let n = m.meta_arity in
  let (env, s) = destruct_prod n Timed.(!(m.meta_type)) in
  let vs = vars env in
  let xs = Array.map _Vari vs in

  let t1 = to_prod env _Type in
  let m1 = fresh_meta t1 n in

  let y = Bindlib.new_var mkfree "y" in
  let env = add y (_Meta m1 xs) None env in
  let t2 = to_prod env (lift s) in
  let m2 = fresh_meta t2 (n+1) in

  let r1 = Bindlib.unbox (_Meta m xs) in
  let p = _Meta m1 xs in
  let q = Bindlib.bind_var y (_Meta m2 (Array.append xs [|_Vari y|])) in
  let r2 = Bindlib.unbox (_Prod p q) in

  let f x = Bindlib.unbox (Bindlib.bind_mvar vs x) in
  r1, r2, f p, f q

(** [make_meta_codomain ctx a] builds a metavariable intended as the  codomain
    type for a product of domain type [a].  It has access to the variables  of
    the context [ctx] and a fresh variables corresponding to the argument. *)
let make_meta_codomain : ctxt -> term -> tbinder = fun ctx a ->
  let x = Bindlib.new_var mkfree "x" in
  let m = Meta(fresh_meta Kind 0, [||]) in
  (* [m] can be instantiated by Type or Kind only (the type of [m] is
     therefore incorrect when [m] is instantiated by Kind. *)
  let b = Basics.make_meta ((x, a, None) :: ctx) m in
  Bindlib.unbox (Bindlib.bind_var x (lift b))

(** Accumulated constraints. *)
let constraints = Stdlib.ref []

(** Function adding a constraint. *)
let conv ctx a b =
  if not (Eval.eq_modulo ctx a b) then
    begin
      if !log_enabled then
        log_infr (yel "add %a") pp_constr (ctx,a,b);
      let open Stdlib in constraints := (ctx,a,b) :: !constraints
    end

(** [infer ctx t] infers a type for the term [t] in context [ctx],
    possibly under some constraints recorded in [constraints] using
    [conv]. The returned type is well-sorted if recorded unification
    constraints are satisfied. [ctx] must be well-formed. This function
    never fails (but constraints may be unsatisfiable). *)
let rec infer : ctxt -> term -> term = fun ctx t ->
  if !log_enabled then log_infr "infer %a%a" pp_ctxt ctx pp_term t;
  match unfold t with
  | Patt(_,_,_) -> assert false (* Forbidden case. *)
  | TEnv(_,_)   -> assert false (* Forbidden case. *)
  | Kind        -> assert false (* Forbidden case. *)
  | Wild        -> assert false (* Forbidden case. *)
  | TRef(_)     -> assert false (* Forbidden case. *)

  (* -------------------
      ctx ⊢ Type ⇒ Kind  *)
  | Type        -> Kind

  (* ---------------------------------
      ctx ⊢ Vari(x) ⇒ Ctxt.find x ctx  *)
  | Vari(x)     ->
      let a = try Ctxt.type_of x ctx with Not_found -> assert false in
      if !log_enabled then log_infr (blu "%a : %a") pp_term t pp_term a;
      a

  (* -------------------------------
      ctx ⊢ Symb(s) ⇒ !(s.sym_type)  *)
  | Symb(s)     ->
      let a = !(s.sym_type) in
      if !log_enabled then log_infr (blu "%a : %a") pp_term t pp_term a;
      a

  (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ b<x> ⇒ s
     -----------------------------------------
                ctx ⊢ Prod(a,b) ⇒ s            *)
  | Prod(a,b)   ->
      (* We ensure that [a] is of type [Type]. *)
      check ctx a Type;
      (* We infer the type of the body, first extending the context. *)
      let (_,b,ctx') = Ctxt.unbind ctx a None b in
      let s = infer ctx' b in
      (* We check that [s] is a sort. *)
      begin
        let s = unfold s in
        match s with
        | Type | Kind -> s
        | _           -> conv ctx s Type; Type
      (* We add the constraint [s = Type] because kinds cannot occur
         inside a term. So, [t] cannot be a kind. *)
      end

  (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ t<x> ⇒ b<x>
     --------------------------------------------
             ctx ⊢ Abst(a,t) ⇒ Prod(a,b)          *)
  | Abst(a,t)   ->
      (* We ensure that [a] is of type [Type]. *)
      check ctx a Type;
      (* We infer the type of the body, first extending the context. *)
      let (x,t,ctx') = Ctxt.unbind ctx a None t in
      let b = infer ctx' t in
      (* We build the product type by binding [x] in [b]. *)
      Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b)))

  (*  ctx ⊢ t ⇒ Prod(a,b)    ctx ⊢ u ⇐ a
     ------------------------------------
         ctx ⊢ Appl(t,u) ⇒ subst b u      *)
  | Appl(t,u)   ->
      (* We first infer a product type for [t]. *)
      let (a,b) =
        let c = Eval.whnf ctx (infer ctx t) in
        match c with
        | Prod(a,b) -> (a,b)
        | Meta(m,ts) ->
            let mxs, p, bp1, bp2 = extend_meta_type m in
            conv ctx mxs p;
            (Bindlib.msubst bp1 ts, Bindlib.msubst bp2 ts)
        | _         ->
            let a = Basics.make_meta ctx Type in
            let b = make_meta_codomain ctx a in
            conv ctx c (Prod(a,b)); (a,b)
      in
      (* We then check the type of [u] against the domain type. *)
      check ctx u a;
      (* We produce the returned type. *)
      Bindlib.subst b u

  (*  ctx ⊢ t ⇐ a       ctx, x : a := t ⊢ u ⇒ b
     -------------------------------------------
        ctx ⊢ let x : a ≔ t in u ⇒ subst b t     *)
  | LLet(a,t,u) ->
      check ctx a Type;
      check ctx t a;
      (* Unbind [u] and enrich context with [x: a ≔ t] *)
      let (x,u,ctx') = Ctxt.unbind ctx a (Some(t)) u in
      let b = infer ctx' u in
      (* Build back the term *)
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Bindlib.subst b t

  (*  ctx ⊢ term_of_meta m e ⇒ a
     ----------------------------
         ctx ⊢ Meta(m,e) ⇒ a      *)
  | Meta(m,ts)   ->
      (* The type of [Meta(m,ts)] is the same as the one obtained by applying
         to [ts] a new symbol having the same type as [m]. *)
      let s = Sign.new_sym (meta_name m) !(m.meta_type) in
      infer ctx (Array.fold_left (fun acc t -> Appl(acc,t)) (Symb s) ts)

(** [check ctx t a] checks that the term [t] has type [a] in context [ctx],
    possibly under some constraints recorded in [constraints] using
    [conv]. [ctx] must be well-formed and [a] well-sorted. This function never
    fails (but constraints may be unsatisfiable). *)
and check : ctxt -> term -> term -> unit = fun ctx t a ->
  if !log_enabled then log_infr "check %a : %a" pp_term t pp_term a;
  conv ctx (infer ctx t) a

(** [infer ctx t] returns a pair [(a,cs)] where [a] is a type for the term [t]
    in the context [ctx] under unification constraints [cs].  In other words,
    the constraints of [cs] must be satisfied for [t] to have type [a]. [ctx]
    must be well-formed. This function never fails (but constraints may be
    unsatisfiable). *)
let infer : ctxt -> term -> term * constr list = fun ctx t ->
  Stdlib.(constraints := []);
  let a = infer ctx t in
  let constrs = Stdlib.(!constraints) in
  if !log_enabled then
    begin
      log_infr (gre "infer %a : %a") pp_term t pp_term a;
      List.iter (log_infr "  if %a" pp_constr) constrs;
    end;
  Stdlib.(constraints := []);
  (a, constrs)

(** [check ctx t a] checks returns a list [cs] of unification
    constraints for [t] to be of type [a] in the context [ctx]. The
    context [ctx] must be well-typed, and the type [c]
    well-sorted. This function never fails (but constraints may be
    unsatisfiable). *)
let check : ctxt -> term -> term -> constr list = fun ctx t a ->
  Stdlib.(constraints := []);
  check ctx t a;
  let constrs = Stdlib.(!constraints) in
  if !log_enabled then
    begin
      log_infr (gre "check %a : %a") pp_term t pp_term a;
      List.iter (log_infr "  if %a" pp_constr) constrs;
    end;
  Stdlib.(constraints := []);
  constrs
