open Common
open Pos
open Lplib
open Timed
open Term

let log = Debug.new_logger 'z' "refi" "Refiner"
let log = log.logger

(** Type for unification constraints solvers. *)
type solver = problem -> constr list option

type coercer = ctxt -> term -> term -> term -> term

(** Module that provide a lookup function to the refiner. *)
module type LOOKUP = sig
  val lookup : coercer -> ctxt -> term -> term -> (term * term * term) option
  (** [lookup cc ctx a b] returns a 3-uple [Some(t_c, dom, arg)] where [t_c]
      is a term of type [r] with [r ≈ b] (where [≈] is not specified), and
      [t_c] is the coercion of a term of type [a] to [b]. The term [t_c] is of
      the form [c ?1 … ?k … ?n] where [c] is a symbol of type [Πx1:T1, …,
      Πxk:Tk, …, Πxn:Tn, r] and where the [k]th argument is a reference (a
      {!constructor:Term.TRef} term) to [arg] which is cast from [Tk] with [Tk
      ≈ a] to [r] (with [r ≈ b]). The function [cc ctx t a b] coerces term [t]
      in context [ctx] from type [a] to [b]. It may be used to coerce
      recursively if needed. *)

  val solve : solver
  (** [solve pb] is specified in {!module:Unif}, see
      {!val:Unif.solve_noexn}. *)
end

module type S = sig
  exception NotTypable
  (** Raised when a term cannot be typed. *)

  val infer : ctxt -> term loc -> term * term
  (** [infer ctx t] returns a tuple [(u, a)] where [a] is the type of [t]
      inferred from context [ctx], [u] is [t] refined. [?pos] is used in error
      messages to indicate the position of [t].
      @raise NotTypable when the type of [t] cannot be inferred. *)

  val check : ?pos:Pos.pos -> ctxt -> term -> term -> term
  (** [check ?pos ctx t a] checks that [t] is of type [a] solving constraints
      with [solver] and returns [t] refined. The parameter [?pos] is used in
      error messages to indicate the position of [t].
      @raise NotTypable if [t] does not have type [a] or type of [t] cannot be
                        inferred. *)

  val check_sort : ctxt -> term loc -> term * term
  (** [type_enforce ctx t] verifies that [t] is a type and returns a tuple
      [(t',s)] where [t'] is [t] refined and [s] is the sort of [t]. *)

  val infer_noexn : constr list -> ctxt -> term ->
    (term * term * constr list) option
  (** [infer_noexn cs ctx t] returns a triplet [(t', t_ty, cs')] where [t_ty]
      is the inferred type of [t] with equations [cs] and in context [ctx],
      [t'] is [t] refined and [cs] is a new list of constraints that must be
      solved so that [t'] has type [t_ty]. If [t] is not typable, [None] is
      returned. *)

  val check_noexn : constr list -> ctxt -> term -> term ->
    (term * constr list) option
  (** [check_noexn ?lg cs ctx t t_ty] ensures that term [t] has type [t_ty] in
      context [ctx] and with equations [cs]. It returns term [t] refined and a
      list of new equations that must be solved. *)
end

module Make : functor (_ : LOOKUP) -> S =
functor
  (L : LOOKUP)
  ->
  struct
    let constraints = Stdlib.ref []

    exception NotTypable

    (** [unif ctx a b] solves the unification problem [ctx ⊢ a ≡ b]. Current
        implementation collects constraints in {!val:constraints} then solves
        them at the end of type checking. *)
    let unif : ctxt -> term -> term -> unit =
     fun ctx a b ->
     if not (Eval.eq_modulo ctx a b) then
     (* NOTE: eq_modulo is used because the unification algorithm counts on
        the fact that no constraint is added in some cases (see test
        "245b.lp"). We may however want to reduce the number of calls to
        [eq_modulo]. *)
       begin
         if !Debug.log_enabled then
           log (Extra.yel "add constraint %a") Print.pp_constr
             (ctx, a, b);
         Stdlib.(constraints := (ctx, a, b) :: !constraints)
       end

    (** [coerce ctx t a b] refines term [t] of type [a] into term of type
        [b]. *)
    let rec coerce : ctxt -> term -> term -> term -> term =
     fun ctx t a b ->
     if !Debug.log_enabled then
       log "Coerce [%a: %a = %a]" Print.pp_term t Print.pp_term a
         Print.pp_term b;
     if Eval.eq_modulo ctx a b then t else
     let eqs = List.rev Stdlib.(!constraints) in
     let pb = {empty_problem with to_solve = (ctx, a, b) :: eqs} in
     match L.solve pb with
     | Some [] -> t
     | None | Some _ ->
     match L.lookup coerce ctx a b with
     | Some (t_c, t_c_ty, arg) ->
         if !(Debug.log_enabled) then
           log (Extra.gre "Coerced \"%a\" to \"%a\"") Print.pp_term t
             Print.pp_term t_c;
         unif ctx arg t; unif ctx b t_c_ty; t_c
     | None ->
         (if !Debug.log_enabled then log (Extra.red "Failed coercion"));
         unif ctx a b; t

    (** [type_enforce ctx a] returns a tuple [(a',s)] where [a'] is refined
        term [a] and [s] is a sort (Type or Kind) such that [a'] is of type
        [s]. *)
    let rec type_enforce : ctxt -> term -> term * term =
     fun ctx a ->
      if !Debug.log_enabled then log "Type enforce [%a]" Print.pp_term a;
      let a, s = infer ctx a in
      let sort =
        match unfold s with
        | Kind -> Kind
        | Type -> Type
        | _ -> Type
        (* FIXME The algorithm should be able to backtrack on the choice of
           this sort, first trying [Type], and if it does not succeed, trying
           [Kind]. *)
      in
      let a = coerce ctx a s sort in
      (a, s)

    (** [force ctx t a] returns a term [t'] such that [t'] has type [a], and
        [t'] is the refinement of [t]. *)
    and force : ctxt -> term -> term -> term =
     fun ctx te ty ->
      if !Debug.log_enabled then
        log "Force [%a] of [%a]" Print.pp_term te Print.pp_term ty;
      let t, a = infer ctx te in
      coerce ctx t a ty

    and infer : ctxt -> term -> term * term =
     fun ctx t ->
      if !Debug.log_enabled then log "Infer [%a]" Print.pp_term t;
      match unfold t with
      | Patt _ -> assert false
      | TEnv _ -> assert false
      | Kind -> assert false
      | Wild -> assert false
      | TRef _ -> assert false
      | Type -> (Type, Kind)
      | Vari x ->
          let a = try Ctxt.type_of x ctx with Not_found -> assert false in
          (t, a)
      | Symb s -> (t, !(s.sym_type))
      (* All metavariables inserted are typed. *)
      | (Meta (m, ts)) as t ->
          let rec ref_esubst i dom =
            (* Refine terms of the explicit substitution. *)
            if i >= Array.length ts then dom else
            match unfold dom with
            | Prod(ai, b) ->
                ts.(i) <- force ctx ts.(i) ai;
                let b = Bindlib.subst b ts.(i) in
                ref_esubst (i + 1) b
            | _ ->
                (* Meta type must be a product of arity greater or equal to
                   the environment *)
                assert false
          in
          let range = ref_esubst 0 !(m.meta_type) in
          (t, range)
      | LLet (t_ty, t, u) ->
          (* Check that [a] is a type, and refine it. *)
          let t_ty, _ = type_enforce ctx t_ty in
          (* Check that [t] is of type [a'], and refine it *)
          let t = force ctx t t_ty in
          (* Unbind [u] and get new context with [x: t_ty ≔ t] *)
          let x, u, ctx = Ctxt.unbind ctx t_ty (Some t) u in
          (* Infer type of [u'] and refine it. *)
          let u, u_ty = infer ctx u in
          let u_ty = Bindlib.(u_ty |> lift |> bind_var x |> unbox) in
          let u_ty = Bindlib.subst u_ty t in
          let u = Bindlib.(u |> lift |> bind_var x |> unbox) in
          (LLet (t_ty, t, u), u_ty)
      | Abst (dom, b) ->
          let dom = force ctx dom Type in
          let x, b, ctx = Ctxt.unbind ctx dom None b in
          let b, range = infer ctx b in
          let b = Bindlib.(lift b |> bind_var x |> unbox) in
          let range = Bindlib.(lift range |> bind_var x |> unbox) in
          (Abst (dom, b), Prod (dom, range))
      | Prod (dom, b) ->
          let dom = force ctx dom Type in
          let x, b, ctx = Ctxt.unbind ctx dom None b in
          let b, b_s = type_enforce ctx b in
          let s =
            match unfold b_s with
            | Type -> Type
            | Kind -> Kind
            | b_s ->
                Error.wrn None
                  "Type error, sort mismatch: there is no rule of the form \
                   (TYPE, %a, _) in λΠ/R" Print.pp_term b_s;
                raise NotTypable

          in
          let b = Bindlib.(lift b |> bind_var x |> unbox) in
          (Prod (dom, b), s)
      | Appl (t, u) -> (
          let t, t_ty = infer ctx t in
          match Eval.whnf ctx t_ty with
          | Prod (dom, b) ->
              let u = force ctx u dom in
              (Appl (t, u), Bindlib.subst b u)
          | Meta (_, _) ->
              let u, u_ty = infer ctx u in
              let range = LibTerm.Meta.make_codomain ctx u_ty in
              unif ctx t_ty (Prod (u_ty, range));
              (Appl (t, u), Bindlib.subst range u)
          | t_ty ->
              (* XXX Slight variation regarding the rule from Matita *)
              let u, u_ty = infer ctx u in
              let range = LibTerm.Meta.make_codomain ctx u_ty in
              let t = coerce ctx t t_ty (Prod (u_ty, range)) in
              (Appl (t, u), Bindlib.subst range u) )

    (** [noexn f cs ctx args] initialises {!val:constraints} to [cs],
        calls [f ctx args] and returns [Some(r,cs)] where [r] is the value of
        the call to [f] and [cs] is the list of constraints gathered by
        [f]. Function [f] may raise [NotTypable], in which case [None] is
        returned. {!val:constraints} is reset before leaving the function. *)
    let noexn : (ctxt -> 'a -> 'b) -> constr list -> ctxt -> 'a ->
      ('b * constr list) option =
      fun f cs ctx args ->
      Stdlib.(constraints := cs);
      let r =
        try
          let r = Debug.time_of (fun () -> f ctx args) in
          let cs = Stdlib.(!constraints) in
          Some(r, List.rev cs)
        with NotTypable -> None
      in Stdlib.(constraints := []); r

    let infer_noexn cs ctx t =
      if !Debug.log_enabled then
        log "Top infer %a%a" Print.pp_ctxt ctx Print.pp_term t;
      Option.map (fun ((t,a), cs) -> (t, a, cs)) ((noexn infer) cs ctx t)

    let check_noexn cs ctx t a =
      if !Debug.log_enabled then log "Top check \"%a\"" Print.pp_typing
          (ctx, t, a);
      let force ctx (t, a) = force ctx t a in
      (noexn force) cs ctx (t, a)

    let infer : ctxt -> term loc -> term * term =
      fun ctx {pos; elt=t} ->
      match infer_noexn [] ctx t with
      | None -> Error.fatal pos "[%a] is not typable." Print.pp_term t
      | Some(t, a, to_solve) ->
          match L.solve {empty_problem with to_solve} with
            | None -> Error.fatal pos "[%a] is not typable."
                        Print.pp_term t
            | Some [] -> (t, a)
            | Some cs ->
                List.iter
                  (Error.wrn pos "Cannot solve [%a].@\n" Print.pp_constr)
                  cs;
                Error.fatal pos "[%a] is not typable." Print.pp_term a

    let check : ?pos:Pos.pos -> ctxt -> term -> term -> term =
      fun ?pos ctx t a ->
      match check_noexn [] ctx t a with
      | None -> Error.fatal pos "[%a] does not have type [%a]."
                  Print.pp_term t Print.pp_term a
      | Some(t, to_solve) ->
          match L.solve {empty_problem with to_solve} with
            | None -> Error.fatal pos "[%a] does not have type [%a]."
                        Print.pp_term t Print.pp_term a
            | Some [] -> t
            | Some cs ->
                List.iter
                  (Error.wrn pos "Cannot solve [%a].\n" Print.pp_constr)
                  cs;
                Error.fatal pos "[%a] does not have type [%a]."
                  Print.pp_term t Print.pp_term a

    let check_sort : ctxt -> term loc -> term * term =
      fun ctx {elt=t; pos} ->
      Stdlib.(constraints := []);
      let t, a = type_enforce ctx t in
      let to_solve = Stdlib.(!constraints) in
      match L.solve {empty_problem with to_solve} with
      | None -> Error.fatal pos "[%a] is not typable" Print.pp_term t
      | Some [] -> t, a
      | Some cs ->
          List.iter (Error.wrn None "Cannot solve [%a].\n" Print.pp_constr)
            cs;
          Error.fatal pos "[%a] is not typable." Print.pp_term a
  end

(** {1 Preset refiners} *)

(** A refiner without coercion generator. *)
module NoCoercion =
  Make(struct let lookup _ _ _ _ = None let solve _ = None end)

(** A reference to a refiner that can be used in other modules. *)
let default : (module S) Stdlib.ref = Stdlib.ref (module NoCoercion: S)
