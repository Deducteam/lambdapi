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

(** [type_app a ts] returns [Some(u)] where [u] is a type of [add_args x ts]
   where [x] is any term of type [a] if [x] can be applied to at least
   [List.length ts] arguments, and [None] otherwise. *)
let rec type_app : ctxt -> term -> term list -> term option = fun ctx a ts ->
  match Eval.whnf ctx a, ts with
  | Prod(_,b), t::ts -> type_app ctx (Bindlib.subst b t) ts
  | _, [] -> Some a
  | _, _ -> None

(** Given a meta [m] of type [Πx1:a1,..,Πxn:an,b], [make_prod m] returns a
   constraint [(c,m[x1;..;xn],a)] where [c=[x1:a1;..;xn:an]],
   [a=Πy:m1[x1;..;xn],m2[x1;..;xn;y], and [m1] and [m2] are fresh metas. *)
let make_prod : meta -> ctxt * tvar array * tbox array * tbox = fun m ->
  if !log_enabled then log_infr "make_prod";
  let n = m.meta_arity in
  let env, s = Env.of_prod [] n !(m.meta_type) in
  let vs = Env.vars env in
  let xs = Array.map _Vari vs in
  (* domain *)
  let u1 = Env.to_prod env _Type in
  let m1 = Meta.fresh u1 n in
  let a = _Meta m1 xs in
  (* codomain *)
  let y = Bindlib.new_var mkfree "y" in
  let env' = Env.add y (_Meta m1 xs) None env in
  let u2 = Env.to_prod env' (lift s) in
  let m2 = Meta.fresh u2 (n+1) in
  let b = Bindlib.bind_var y (_Meta m2 (Array.append xs [|_Vari y|])) in
  (* result *)
  (Env.to_ctxt env, vs, xs, _Prod a b)

(** Accumulated constraints. *)
let constraints = Stdlib.ref []

(** Function adding a constraint. *)
let conv ctx a b =
  if not (Eval.eq_modulo ctx a b) then
    begin
      let c = (ctx,a,b) in
      Stdlib.(constraints := c::!constraints);
      if !log_enabled then log_infr (yel "add %a") pp_constr c
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
      (* Here, we force [s] to be equivalent to [Type] as there is little
         chance (no?) that it can be a kind. FIXME? *)
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
      let rec get_prod f typ =
        match unfold typ with
        | Prod(a,b) -> (a,b)
        | Meta(m,_) -> (* Set |m] to a product. *)
            let _cont, vs, _xs, p = make_prod m in
            if !log_enabled then
              log_infr "%a ≔ %a" pp_meta m pp_term (Bindlib.unbox p);
            Meta.set m (Bindlib.unbox (Bindlib.bind_mvar vs p));
            get_prod f typ
        | _ -> f typ
      in
      let get_prod_whnf = get_prod (fun _ -> raise NotTypable) in
        (*let a = LibTerm.Meta.make ctx Type in
        (* Here, we force [b] to be of type [Type] as there is little
           (no?) chance that it can be a kind. FIXME? *)
        let b = LibTerm.Meta.make_codomain ctx a in
        conv ctx t (Prod(a,b)); (a,b)*)
      let get_prod = get_prod (fun t -> get_prod_whnf (Eval.whnf ctx t)) in
      let (a,b) = get_prod (infer ctx t) in
      check ctx u a;
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
      let s = Term.create_sym (Sign.current_path()) Privat Const
                Eager true ("?" ^ Meta.name m) !(m.meta_type) [] in
      infer ctx (Array.fold_left (fun acc t -> Appl(acc,t)) (Symb s) ts)
      (*let rec infer_app typ ts =
        match typ, ts with
        | _, [] -> typ
        | Prod(a,b), t::ts -> check ctx t a; infer_app (Bindlib.subst b t) ts
        | _, _ -> assert false
      in infer_app !(m.meta_type) (Array.to_list ts)*)

(** [check ctx t a] checks that the term [t] has type [a] in context
   [ctx], possibly under some constraints recorded in [constraints] using
   [conv]. [ctx] must be well-formed and [a] well-sorted. This function never
   fails (but constraints may be unsatisfiable). *)
and check : ctxt -> term -> term -> unit = fun ctx t a ->
  if !log_enabled then log_infr "check %a" pp_typing (ctx,t,a);
  conv ctx (infer ctx t) a

(** [infer_noexn cs ctx t] returns [None] if the type of [t] in context [ctx]
   and constraints [cs] cannot be infered, or [Some(a,cs')] where [a] is some
   type of [t] in the context [ctx] if the constraints [cs'] are satisfiable
   (which may not be the case). [ctx] must well sorted. *)
let infer_noexn :
    ?lg:logger -> constr list -> ctxt -> term -> (term * constr list) option =
  fun ?(lg=logger_hndl) cs ctx t ->
  Stdlib.(constraints := cs);
  let res =
    try
      if !log_enabled then lg.logger "infer %a%a" pp_ctxt ctx pp_term t;
      let t0 = Sys.time() in
      let a = infer ctx t in
      let cs = List.rev Stdlib.(!constraints) in
      (if !log_enabled then
        let cond oc c = Format.fprintf oc "\n  ; %a" pp_constr c in
        lg.logger (gre "%f\n  %a%a")
          (Sys.time() -. t0) pp_term a (List.pp cond "") cs);
      Some (a, cs)
    with NotTypable -> None
  in Stdlib.(constraints := []); res

(** [check_noexn cs ctx t a] returns [None] if [t] does not have type [a] in
   context [ctx] and constraints [cs], and [Some(cs')] where [cs'] is a list
   of constraints under which [t] may have type [a] (but constraints may be
   unsatisfiable). The context [ctx] and the type [a] must be well sorted. *)
let check_noexn :
    ?lg:logger -> constr list -> ctxt -> term -> term -> constr list option =
  fun ?(lg=logger_hndl) cs ctx t a ->
  Stdlib.(constraints := cs);
  let res =
    try
      if !log_enabled then lg.logger "check %a" pp_typing (ctx,t,a);
      let t0 = Sys.time() in
      check ctx t a;
      let cs = List.rev Stdlib.(!constraints) in
      (if !log_enabled then
        let cond oc c = Format.fprintf oc "\n  ; %a" pp_constr c in
        lg.logger (gre "%f%a") (Sys.time() -. t0) (List.pp cond "") cs);
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
  match infer_noexn [] ctx t with
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
  match check_noexn [] ctx t a with
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
  match infer_noexn [] ctx t with
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
