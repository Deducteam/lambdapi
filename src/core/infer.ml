(** Generating constraints for type inference and type checking. *)

open Timed
open Console
open Terms
open Print

(** Logging function for typing. *)
let log_infr = new_logger 'i' "infr" "type inference/checking"
let log_infr = log_infr.logger

(** Accumulated constraints. *)
let constraints = Pervasives.ref []

(** Function adding a constraint. *)
let conv ctx a b =
  if not (Basics.eq a b) then
    begin
      if !log_enabled then log_infr (yel "add %a") pp_constr (ctx,a,b);
      let open Pervasives in constraints := (ctx,a,b) :: !constraints
    end

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

(** [infer ctx t] infers a type for the term [t] in context [ctx],
   possibly under some constraints recorded in [constraints] using
   [conv]. The returned type is well-sorted if recorded unification
   constraints are satisfied. [ctx] must be well-formed. This function
   never fails (but constraints may be unsatisfiable). *)
let rec infer : ctxt -> term -> term = fun ctx t ->
  if !log_enabled then log_infr "infer [%a]" pp t;
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
  | Vari(x)     -> (try Basics.type_of x ctx with Not_found -> assert false)

  (* -------------------------------
      ctx ⊢ Symb(s) ⇒ !(s.sym_type)  *)
  | Symb(s,_)   -> !(s.sym_type)

  (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ b<x> ⇒ s
     -----------------------------------------
                ctx ⊢ Prod(a,b) ⇒ s            *)
  | Prod(a,b)   ->
      (* We ensure that [a] is of type [Type]. *)
      check ctx a Type;
      (* We infer the type of the body, first extending the context. *)

      let (_,b,ctx') = Basics.ctx_unbind ctx a None b in
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
      let (x,t,ctx') = Basics.ctx_unbind ctx a None t in
      let b = infer ctx' t in
      (* We build the product type by binding [x] in [b]. *)
      Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b)))

  (*  ctx ⊢ t ⇒ Prod(a,b)    ctx ⊢ u ⇐ a
     ------------------------------------
         ctx ⊢ Appl(t,u) ⇒ subst b u      *)
  | Appl(t,u)   ->
      (* We first infer a product type for [t]. *)
      let (a,b) =
        let c = Eval.whnf (infer ctx t) in
        match c with
        | Prod(a,b) -> (a,b)
        | Meta(_,ts) ->
            let ctx =
              match Basics.distinct_vars ts with
              | None -> ctx
              | Some vs -> Basics.subctx ctx vs
            in
            let a = Basics.make_meta ctx Type in
            let b = make_meta_codomain ctx a in
            conv ctx c (Prod(a,b)); (a,b)
        | _         ->
            let a = Basics.make_meta ctx Type in
            let b = make_meta_codomain ctx a in
            conv ctx c (Prod(a,b)); (a,b)
      in
      (* We then check the type of [u] against the domain type. *)
      check ctx u a;
      (* We produce the returned type. *)
      Bindlib.subst b u

  (*  ctx ⊢ t ⇐ a       ctx, x := t : a ⊢ u ⇒ b
     -------------------------------------------
        ctx ⊢ let x ≔ t : a in u ⇒ subst b t     *)
  | LLet(t,a,u) ->
      check ctx t a;
      (* Unbind [u] and enrich context with [x:=t:a] *)
      let (x,u,ctx') = Basics.ctx_unbind ctx a (Some(t)) u in
      let b = infer ctx' u in
      (* Build back the term *)
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Bindlib.subst b t

  (*  ctx ⊢ term_of_meta m e ⇒ a
     ----------------------------
         ctx ⊢ Meta(m,e) ⇒ a      *)
  | Meta(m,e)   ->
      if !log_enabled then
        log_infr (yel "%s is of type [%a]") (meta_name m) pp !(m.meta_type);
      infer ctx (term_of_meta m e)

(** [check ctx t c] checks that the term [t] has type [c] in context
   [ctx], possibly under some constraints recorded in [constraints]
   using [conv]. [ctx] must be well-formed and [c] well-sorted. This
   function never fails (but constraints may be unsatisfiable). *)

(* [check ctx t c] could be reduced to the default case [conv
   (infer ctx t) c]. We however provide some more efficient
   code when [t] is an abstraction, as witnessed by 'make holide':

   Finished in 3:56.61 at 99% with 3180096Kb of RAM

   Finished in 3:46.13 at 99% with 2724844Kb of RAM

   This avoids to build a product to destructure it just after. *)
and check : ctxt -> term -> term -> unit = fun ctx t c ->
  if !log_enabled then log_infr "check [%a] [%a]" pp t pp c;
  match unfold t with
  (*  c → Prod(d,b)    a ~ d    ctx, x : A ⊢ t<x> ⇐ b<x>
      ----------------------------------------------------
                         ctx ⊢ Abst(a,t) ⇐ c                   *)
  | Abst(a,t)   ->
      (* We ensure that [a] is of type [Type]. *)
      check ctx a Type;
      (* We (hopefully) evaluate [c] to a product, and get its body. *)
      let b =
        let c = Eval.whnf c in
        match c with
        | Prod(d,b) -> conv ctx d a; b (* Domains must be convertible. *)
        | Meta(_,ts) ->
           let ctx =
             match Basics.distinct_vars ts with
             | None -> ctx
             | Some vs -> Basics.subctx ctx vs
           in
           let b = make_meta_codomain ctx a in
           conv ctx c (Prod(a,b)); b
        | _         -> (* Generate product type with codomain [a]. *)
           let b = make_meta_codomain ctx a in
           conv ctx c (Prod(a,b)); b
      in
      (* We type-check the body with the codomain. *)
      let (x,t,ctx') = Basics.ctx_unbind ctx a None t in
      check ctx' t (Bindlib.subst b (Vari(x)))
  | t           ->
      (*  ctx ⊢ t ⇒ a
         -------------
          ctx ⊢ t ⇐ a  *)
      conv ctx (infer ctx t) c

(** [infer ctx t] returns a pair [(a,cs)] where [a] is a type for the
   term [t] in the context [ctx], under unification constraints [cs].
   In other words, the constraints of [cs] must be satisfied for [t]
   to have type [a]. [ctx] must be well-formed. This function never
   fails (but constraints may be unsatisfiable). *)
let infer : ctxt -> term -> term * unif_constrs = fun ctx t ->
  Pervasives.(constraints := []);
  let a = infer ctx t in
  let constrs = Pervasives.(!constraints) in
  if !log_enabled then
    begin
      log_infr (gre "infer [%a] yields [%a]") pp t pp a;
      List.iter (log_infr "  assuming %a" pp_constr) constrs;
    end;
  Pervasives.(constraints := []);
  (a, constrs)

(** [check ctx t c] checks returns a list [cs] of unification
   constraints for [t] to be of type [c] in the context [ctx]. The
   context [ctx] must be well-typed, and the type [c]
   well-sorted. This function never fails (but constraints may be
   unsatisfiable). *)
let check : ctxt -> term -> term -> unif_constrs = fun ctx t c ->
  Pervasives.(constraints := []);
  check ctx t c;
  let constrs = Pervasives.(!constraints) in
  if !log_enabled then
    begin
      log_infr (gre "check [%a] [%a]") pp t pp c;
      List.iter (log_infr "  assuming %a" pp_constr) constrs;
    end;
  Pervasives.(constraints := []);
  constrs
