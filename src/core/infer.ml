(** Generating constraints for type inference and type checking. *)

open Timed
open Common
open Console
open Term
open Print
open Lplib

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

(** Accumulated constraints. *)
let constraints = Stdlib.ref []

(** Function adding a constraint. *)
let conv ctx a b =
  if not (List.mem_sorted LibTerm.cmp_constr (ctx,a,b)
            Stdlib.(!constraints)) && not (Eval.eq_modulo ctx a b) then
    begin
      if !log_enabled then log_infr (yel "add %a") pp_constr (ctx,a,b);
      Stdlib.(constraints :=
                Lplib.List.insert LibTerm.cmp_constr (ctx,a,b) !constraints)
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
      (* We first infer a product type for [t]. *)
      let (a,b) =
        let c = Eval.whnf ctx (infer ctx t) in
        match c with
        | Prod(a,b) -> (a,b)
        | _         ->
            let a = LibTerm.make_meta ctx Type in
            (* Here, we force [b] to be of type [Type] as there is little
               (no?) chance that it can be a kind. FIXME? *)
            let b = LibTerm.make_meta_codomain ctx a in
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
      let s = Term.create_sym (Sign.current_sign()).sign_path
                Privat Defin Eager false (Meta.name m) !(m.meta_type) [] in
      infer ctx (Array.fold_left (fun acc t -> Appl(acc,t)) (Symb s) ts)

(** [check ctx t a] checks that the term [t] has type [a] in context
   [ctx], possibly under some constraints recorded in [constraints] using
   [conv]. [ctx] must be well-formed and [a] well-sorted. This function never
   fails (but constraints may be unsatisfiable). *)
and check : ctxt -> term -> term -> unit = fun ctx t a ->
  if !log_enabled then
    log_infr "check %a%a\n: %a" pp_ctxt ctx pp_term t pp_term a;
  conv ctx (infer ctx t) a

(** [infer_noexn cs ctx t] returns [None] if the type of [t] in context [ctx]
   and constraints [cs] cannot be infered, or [Some(a,cs')] where [a] is some
   type of [t] in the context [ctx] if the constraints [cs'] are satisfiable
   (which may not be the case). [ctx] must well sorted. *)
let infer_noexn : constr list -> ctxt -> term -> (term * constr list) option =
  fun cs ctx t ->
  Stdlib.(constraints := cs);
  let res =
    try
      let a = infer ctx t in
      let cs = Stdlib.(!constraints) in
      (if !log_enabled then
        let cond oc c = Format.fprintf oc "\n  if %a" pp_constr c in
        log_infr (gre "infer %a : %a%a")
          pp_term t pp_term a (List.pp cond "") cs);
      Some (a,cs)
    with NotTypable -> None
  in Stdlib.(constraints := []); res

(** [check_noexn cs ctx t a] returns [None] if [t] does not have type [a] in
   context [ctx] and constraints [cs], and [Some(cs')] where [cs'] is a list
   of constraints under which [t] may have type [a] (but constraints may be
   unsatisfiable). The context [ctx] and the type [a] must be well sorted. *)
let check_noexn : constr list -> ctxt -> term -> term -> constr list option =
  fun cs ctx t a ->
  Stdlib.(constraints := cs);
  let res =
    try
      check ctx t a;
      let cs = Stdlib.(!constraints) in
      (if !log_enabled then
        let cond oc c = Format.fprintf oc "\n  if %a" pp_constr c in
        log_infr (gre "check %a\n: %a%a")
          pp_term t pp_term a (List.pp cond "") cs);
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
