(** Generating constraints for type inference and type checking. *)

open Timed
open Console
open Terms
open Env
open Print

(** Logging function for typing. *)
let log_infr = new_logger 'i' "infr" "type inference/checking"
let log_infr = log_infr.logger

(** [destruct_prod n prod] returns a tuple [(env,a)] where [a] is constructed
   from the term [prod] by destructing (i.e., by unbinding with the [Bindlib]
   terminology) [n] dependent products. The free variables created by this
   process are given (with their types) in the environment [env] (in reverse
   order). The function raises [Invalid_argument] if [prod] does not evaluate
   to a series of (at least) [n] product types. Intuitively, if the term
   [prod] is of the form [Πx1:a1, ⋯, Πxn:an, a] then the function (roughly)
   returns [a], and the environment [(xn,an); ⋯;(x1,a1)] (note the reserve
   order). *)
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

(** Given a metavariable [m] of arity [n] and type [Πx1:A1,..,Πxn:An,B] (with
   [B] being a sort normally), [extend_meta_type m] returns
   [m[x1,..,xn],(Πy:p,q),bp,bq] where p=m1[x1,..,xn], q=m2[x1,..,xn,y], bp is
   a mbinder of [x1,..,xn] over p, and bq is a mbinder of [x1,..,xn] over q,
   where [y] is a fresh variable, and [m1] and [m2] are fresh metavariables of
   arity [n] and [n+1], and type [Πx1:A1,..,Πxn:An,TYPE] and
   [Πx1:A1,..,Πxn:An,Πy:m1[x1,..,xn],B] respectively. *)
let extend_meta_type : meta -> env * term * term *
    tmbinder * (term, tbinder) Bindlib.mbinder = fun m ->
  let n = m.meta_arity in
  let (env, s) = destruct_prod n Timed.(!(m.meta_type)) in
  let vs = vars env in
  let xs = Array.map _Vari vs in

  let t1 = to_prod env _Type in
  let m1 = Meta.fresh t1 n in

  let y = Bindlib.new_var mkfree "y" in
  let env' = add y (_Meta m1 xs) None env in
  let t2 = to_prod env' (lift s) in
  let m2 = Meta.fresh t2 (n+1) in

  let r1 = Bindlib.unbox (_Meta m xs) in
  let p = _Meta m1 xs in
  let q = Bindlib.bind_var y (_Meta m2 (Array.append xs [|_Vari y|])) in
  let r2 = Bindlib.unbox (_Prod p q) in

  let f x = Bindlib.unbox (Bindlib.bind_mvar vs x) in
  env, r1, r2, f p, f q

(** [type_app a ts] returns the type of [add_args x ts] where [x] is any
    term of type [a], if it exists. *)
let rec type_app : ctxt -> term -> term list -> term option =
  fun ctx a ts ->
  match (Eval.whnf ctx a), ts with
  | Prod(_,b), t :: ts -> type_app ctx (Bindlib.subst b t) ts
  | _, [] -> Some a
  | _, _ -> None

(** [make_meta_codomain ctx a] builds a metavariable intended as the  codomain
    type for a product of domain type [a].  It has access to the variables  of
    the context [ctx] and a fresh variables corresponding to the argument. *)
let make_meta_codomain : ctxt -> term -> tbinder = fun ctx a ->
  let x = Bindlib.new_var mkfree "x" in
  let m = Meta(Meta.fresh Kind 0, [||]) in
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

(** Exception that may be raised by type inference. *)
exception NotTypable

(** [infer ctx t] tries to infer a type for the term [t] in context [ctx],
   possibly under some constraints recorded in [constraints] using [conv]. The
   returned type is well-sorted if the recorded constraints are
   satisfied. [ctx] must be well sorted.

@raise NotTypable when the term is not typable (when encountering an
   abstraction over a kind). *)
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
        | _           -> conv ctx' s Type; Type
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
      begin
        match unfold b with
        | Kind ->
            wrn None "Abstraction on [%a] is not allowed." Print.pp_term t;
            raise NotTypable
        | _ -> Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b)))
      end

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
            let env, mxs, p, bp1, bp2 = extend_meta_type m in
            let ctx' = Env.to_ctxt env in
            conv ctx' mxs p;
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
      let s = Sign.create_sym Privat Defin (Meta.name m) !(m.meta_type) [] in
      infer ctx (Array.fold_left (fun acc t -> Appl(acc,t)) (Symb s) ts)

(** [check ctx t a] checks that the term [t] has type [a] in context
   [ctx], possibly under some constraints recorded in [constraints] using
   [conv]. [ctx] must be well-formed and [a] well-sorted. This function never
   fails (but constraints may be unsatisfiable). *)
and check : ctxt -> term -> term -> unit = fun ctx t a ->
  if !log_enabled then
    log_infr "check %a%a : %a" pp_ctxt ctx pp_term t pp_term a;
  conv ctx (infer ctx t) a

(** [infer_noexn ctx t] returns [None] if the type of [t] in context [ctx]
   cannot be infered, or [Some(a,cs)] where [a] is some type of [t] in the
   context [ctx] if the constraints [cs] are satisfiable (which may not be the
   case). [ctx] must well sorted. *)
let infer_noexn : ctxt -> term -> (term * constr list) option = fun ctx t ->
  let res =
    try
      Stdlib.(constraints := []);
      let a = infer ctx t in
      let cs = Stdlib.(!constraints) in
      let cs = List.sort_uniq Eval.compare_constr cs in
      if !log_enabled then
        begin
          log_infr (gre "infer %a : %a") pp_term t pp_term a;
          List.iter (log_infr "  if %a" pp_constr) cs;
        end;
      Some (a,cs)
    with NotTypable -> None
  in Stdlib.(constraints := []); res

(** [check_noexn ctx t a] returns [None] if [t] does not have type [a] in
   context [ctx] and [Some(cs)] where [cs] is a list of constraints under
   which [t] may have type [a] (but constraints may be unsatisfiable). The
   context [ctx] and the type [a] must be well sorted. *)
let check_noexn : ctxt -> term -> term -> constr list option = fun ctx t a ->
  let res =
    try
      Stdlib.(constraints := []);
      check ctx t a;
      let cs = Stdlib.(!constraints) in
      if !log_enabled then
        begin
          log_infr (gre "check %a : %a") pp_term t pp_term a;
          List.iter (log_infr "  if %a" pp_constr) cs;
        end;
      Stdlib.(constraints := []);
      Some cs
    with NotTypable -> None
  in Stdlib.(constraints := []); res

(** Type for unification constraints solvers. *)
type solver = problem -> constr list option

(** [infer solve pos ctx t] returns a type for [t] in context [ctx] if there
   is one, using the constraint solver [solve].
@raise Fatal otherwise. [ctx] must well sorted. *)
let infer : solver -> Pos.popt -> ctxt -> term -> term =
  fun solve_noexn pos ctx t ->
  match infer_noexn ctx t with
  | None -> fatal pos "[%a] is not typable." pp_term t
  | Some(a, to_solve) ->
      match solve_noexn {empty_problem with to_solve} with
      | None -> fatal pos "[%a] is not typable." pp_term t
      | Some [] -> a
      | Some cs ->
          List.iter (wrn pos "Cannot solve [%a].\n" pp_constr) cs;
          fatal pos "[%a] is not typable." pp_term a

(** [check pos ctx t a] checks that [t] has type [a] in context [ctx],
using the constraint solver [solve].
@raise Fatal otherwise. [ctx] must well sorted. *)
let check : solver -> Pos.popt -> ctxt -> term -> term -> unit =
  fun solve_noexn pos ctx t a ->
  match check_noexn ctx t a with
  | None -> fatal pos "[%a] does not have type [%a]." pp_term t pp_term a
  | Some(to_solve) ->
      match solve_noexn {empty_problem with to_solve} with
      | None -> fatal pos "[%a] does not have type [%a]." pp_term t pp_term a
      | Some [] -> ()
      | Some cs ->
          List.iter (wrn pos "Cannot solve [%a].\n" pp_constr) cs;
          fatal pos "[%a] does not have type [%a]." pp_term t pp_term a

(** [check_sort pos ctx t] checks that [t] has type [Type] or [Kind] in
   context [ctx], using the constraint solver [solve].
@raise Fatal otherwise. [ctx] must well sorted. *)
let check_sort : solver -> Pos.popt -> ctxt -> term -> unit
  = fun solve_noexn pos ctx t ->
  match infer_noexn ctx t with
  | None -> fatal pos "[%a] is not typable." pp_term t
  | Some(a, to_solve) ->
      match solve_noexn {empty_problem with to_solve} with
      | None -> fatal pos "[%a] is not typable." pp_term t
      | Some ((_::_) as cs) ->
          List.iter (wrn pos "Cannot solve [%a].\n" pp_constr) cs;
          fatal pos "[%a] is not typable." pp_term a
      | Some [] ->
          match unfold a with
          | Type | Kind -> ()
          | _ -> fatal pos "[%a] has type [%a] and not a sort."
                   pp_term t pp_term a
