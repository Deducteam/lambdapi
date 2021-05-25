(** Generating constraints for type inference and type checking. *)

open Timed
open Common
open Error
open Term
open Print
open Debug
open Lplib
open Extra

(** Logging function for typing. *)
let log_infr = new_logger 'i' "infr" "type inference/checking"
let log_infr = log_infr.logger

(** Given a meta [m] of type [Πx1:a1,..,Πxn:an,b], [set_to_prod p m] sets [m]
   to a product term of the form [Πy:m1[x1;..;xn],m2[x1;..;xn;y]] with [m1]
   and [m2] fresh metavariables, and adds these metavariables to [p]. *)
let set_to_prod : problem -> meta -> unit = fun p m ->
  let n = m.meta_arity in
  let env, s = Env.of_prod_nth [] n !(m.meta_type) in
  let vs = Env.vars env in
  let xs = Array.map _Vari vs in
  (* domain *)
  let u1 = Env.to_prod env _Type in
  let m1 = LibMeta.fresh p u1 n in
  let a = _Meta m1 xs in
  (* codomain *)
  let y = new_tvar "y" in
  let env' = Env.add y (_Meta m1 xs) None env in
  let u2 = Env.to_prod env' (lift s) in
  let m2 = LibMeta.fresh p u2 (n+1) in
  let b = Bindlib.bind_var y (_Meta m2 (Array.append xs [|_Vari y|])) in
  (* result *)
  let r = _Prod a b in
  if !log_enabled then log_infr "%a ≔ %a" pp_meta m pp_term (Bindlib.unbox r);
  LibMeta.set p m (Bindlib.unbox (Bindlib.bind_mvar vs r))

(** [conv p ctx a b] adds the the constraint [(ctx,a,b)] in [p], if [a] and
   [b] are not convertible. *)
let conv : problem -> ctxt -> term -> term -> unit = fun p ctx a b ->
  if not (Eval.eq_modulo ctx a b) then
    begin
      let c = (ctx,a,b) in
      p := {!p with to_solve = c::!p.to_solve};
      if !log_enabled then log_infr (mag "add constraint %a") pp_constr c
    end

(** Exception that may be raised by type inference. *)
exception NotTypable

(*TODO make infer tail-recursive. *)
(** [infer p ctx t] tries to infer a type for the term [t] in context [ctx],
   possibly adding new unification constraints in [p]. The set of
   metavariables of [p] are updated if some metavariables are instantiated or
   created. The returned type is well-sorted if the recorded constraints are
   satisfied. [ctx] must be well sorted.
@raise NotTypable when the term is not typable (when encountering an
   abstraction over a kind). *)
let rec infer : problem -> ctxt -> term -> term = fun p ctx t ->
  if !log_enabled then log_infr "infer %a%a" pp_ctxt ctx pp_term t;
  match unfold t with
  | Patt(_,_,_) -> assert false (* Forbidden case. *)
  | TEnv(_,_)   -> assert false (* Forbidden case. *)
  | Kind        -> assert false (* Forbidden case. *)
  | Wild        -> assert false (* Forbidden case. *)
  | TRef(_)     -> assert false (* Forbidden case. *)

  (* -------------------
      ctx ⊢ Type ⇒ Kind  *)
  | Type        -> mk_Kind

  (* ---------------------------------
      ctx ⊢ Vari(x) ⇒ Ctxt.find x ctx  *)
  | Vari(x)     ->
      let a = try Ctxt.type_of x ctx with Not_found -> assert false in
      if !log_enabled then log_infr (yel "%a : %a") pp_term t pp_term a;
      a

  (* -------------------------------
      ctx ⊢ Symb(s) ⇒ !(s.sym_type)  *)
  | Symb(s)     ->
      let a = !(s.sym_type) in
      if !log_enabled then log_infr (yel "%a : %a") pp_term t pp_term a;
      a

  (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ b<x> ⇒ s
     -----------------------------------------
                ctx ⊢ Prod(a,b) ⇒ s            *)
  | Prod(a,b)   ->
      (* We ensure that [a] is of type [Type]. *)
      check p ctx a mk_Type;
      (* We infer the type of the body, first extending the context. *)
      let (_,b,ctx') = Ctxt.unbind ctx a None b in
      let s = infer p ctx' b in
      (* We check that [s] is a sort. *)
      begin
        let s = unfold s in
        match s with
        | Type | Kind -> s
        | _ -> conv p ctx' s mk_Type; mk_Type
      (* Here, we force [s] to be equivalent to [Type] as there is little
         (no?) chance that it can be a kind. *)
      end

  (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ t<x> ⇒ b<x>
     --------------------------------------------
             ctx ⊢ Abst(a,t) ⇒ Prod(a,b)          *)
  | Abst(a,t)   ->
      (* We ensure that [a] is of type [Type]. *)
      check p ctx a mk_Type;
      (* We infer the type of the body, first extending the context. *)
      let (x,t,ctx') = Ctxt.unbind ctx a None t in
      let b = infer p ctx' t in
      begin
        match unfold b with
        | Kind ->
            wrn None "Abstraction on [%a] is not allowed." Print.pp_term t;
            raise NotTypable
        | _ -> mk_Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b)))
      end

  (*  ctx ⊢ t ⇒ Prod(a,b)    ctx ⊢ u ⇐ a
     ------------------------------------
         ctx ⊢ Appl(t,u) ⇒ subst b u      *)
  | Appl(t,u)   ->
      (* [get_prod f typ] returns the domain and codomain of [t] if [t] is a
         product. If [t] is a metavariable, then it instantiates it with a
         product calls [get_prod f typ] again. Otherwise, it calls [f typ]. *)
      let rec get_prod f typ =
        if !log_enabled then log_infr "get_prod %a" pp_term typ;
        match unfold typ with
        | Prod(a,b) -> (a,b)
        | Meta(m,_) -> set_to_prod p m; get_prod f typ
        | _ -> f typ
      in
      let get_prod_whnf = (* assumes that its argument is in whnf *)
        get_prod (fun typ ->
            let a = LibMeta.make p ctx mk_Type in
            (* We force [b] to be of type [Type] as there is little (no?)
               chance that it can be a kind. *)
            let b = LibMeta.make_codomain p ctx a in
            conv p ctx typ (mk_Prod(a,b)); (a,b)) in
      let get_prod =
        get_prod (fun typ -> get_prod_whnf (Eval.whnf ctx typ)) in
      let (a,b) = get_prod (infer p ctx t) in
      check p ctx u a;
      Bindlib.subst b u

  (*  ctx ⊢ t ⇐ a       ctx, x : a := t ⊢ u ⇒ b
     -------------------------------------------
        ctx ⊢ let x : a ≔ t in u ⇒ subst b t     *)
  | LLet(a,t,u) ->
      check p ctx a mk_Type;
      check p ctx t a;
      (* Unbind [u] and enrich context with [x: a ≔ t] *)
      let (x,u,ctx') = Ctxt.unbind ctx a (Some(t)) u in
      let b = infer p ctx' u in
      (* Build back the term *)
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Bindlib.subst b t

  (*  ctx ⊢ term_of_meta m e ⇒ a
     ----------------------------
         ctx ⊢ Meta(m,e) ⇒ a      *)
  | Meta(m,ts)   ->
      (* The type of [Meta(m,ts)] is the same as the one obtained by applying
         to [ts] a new symbol having the same type as [m]. *)
      let s = Term.create_sym (Sign.current_path()) Privat Const
                Eager true ("?" ^ LibMeta.name m) !(m.meta_type) [] in
      infer p ctx
        (Array.fold_left (fun acc t -> mk_Appl(acc,t)) (mk_Symb s) ts)

(** [check ctx t a] checks that the term [t] has type [a] in context [ctx],
   possibly adding new unification constraints in [p]. [ctx] must be
   well-formed and [a] well-sorted.
@raise NotTypable when the term is not typable (when encountering an
   abstraction over a kind). *)
and check : problem -> ctxt -> term -> term -> unit = fun p ctx t a ->
  if !log_enabled then log_infr "check %a" pp_typing (ctx,t,a);
  conv p ctx (infer p ctx t) a

(** [infer_noexn p ctx t] returns [None] if the type of [t] in context [ctx]
   cannot be inferred, or [Some a] where [a] is some type of [t] in the
   context [ctx], possibly adding new constraints in [p]. The metavariables of
   [p] are updated when a metavariable is instantiated or created. [ctx] must
   be well sorted. *)
let infer_noexn : problem -> ctxt -> term -> term option = fun p ctx t ->
  try
    if !log_enabled then
      log_hndl (blu "infer_noexn %a%a") pp_ctxt ctx pp_term t;
    let a = time_of (fun () -> infer p ctx t) in
    if !log_enabled then
      log_hndl (blu "result of infer_noexn:\n%a%a")
        pp_term a pp_constrs !p.to_solve;
    Some a
  with NotTypable -> None

(** [check_noexn p ctx t a] tells whether the term [t] has type [a] in the
   context [ctx], possibly adding new constraints in |p]. The metavariables of
   [p] are updated when a metavariable is instantiated or created. The context
   [ctx] and the type [a] must be well sorted. *)
let check_noexn : problem -> ctxt -> term -> term -> bool = fun p ctx t a ->
  try
    if !log_enabled then log_hndl (blu "check_noexn %a") pp_typing (ctx,t,a);
    time_of (fun () -> check p ctx t a);
    if !log_enabled && !p.to_solve <> [] then
      log_hndl (blu "result of check_noexn:%a") pp_constrs !p.to_solve;
    true
  with NotTypable -> false
