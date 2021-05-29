(** Type inference and checking *)

open Common
open Lplib
open Term
open Timed

(** Logging function for typing. *)
let log = Logger.make 'i' "infr" "type inference/checking"
let log = log.pp

(** Exception that may be raised by type inference. *)
exception NotTypable

(** [unif pb c a b] solves the unification problem [c ⊢ a ≡ b]. Current
    implementation collects constraints in {!val:constraints} then solves
    them at the end of type checking. *)
let unif : problem -> ctxt -> term -> term -> unit =
 fun pb c a b ->
 if not (Eval.pure_eq_modulo c a b) then
 (* NOTE: eq_modulo is used because the unification algorithm counts on
    the fact that no constraint is added in some cases (see test
    "245b.lp"). We may however want to reduce the number of calls to
    [eq_modulo]. *)
   begin
     if Logger.log_enabled () then
       log (Color.yel "add constraint %a") Print.pp_constr
         (c, a, b);
     pb := {!pb with to_solve = (c, a, b) :: !pb.to_solve}
   end

(** {1 Handling coercions} *)

(* Simply unify types, no coercions yet. *)
let coerce pb c t a b = unif pb c a b; t

(** {1 Other rules} *)

(** [type_enforce pb c a] returns a tuple [(a',s)] where [a'] is refined
    term [a] and [s] is a sort (Type or Kind) such that [a'] is of type
    [s]. *)
let rec type_enforce : problem -> ctxt -> term -> term * term =
 fun pb c a ->
  if Logger.log_enabled () then log "Type enforce [%a]" Print.pp_term a;
  let a, s = infer pb c a in
  let sort =
    match unfold s with
    | Kind -> mk_Kind
    | Type -> mk_Type
    | _ -> mk_Type
    (* FIXME The algorithm should be able to backtrack on the choice of
       this sort, first trying [Type], and if it does not succeed, trying
       [Kind]. *)
  in
  let a = coerce pb c a s sort in
  (a, sort)

(** [force pb c t a] returns a term [t'] such that [t'] has type [a],
    and [t'] is the refinement of [t]. *)
and force : problem -> ctxt -> term -> term -> term =
 fun pb c te ty ->
 if Logger.log_enabled () then
   log "Force [%a] of [%a]" Print.pp_term te Print.pp_term ty;
 let (t, a) = infer pb c te in
 coerce pb c t a ty

and infer_aux : problem -> ctxt -> term -> term * term =
 fun pb c t ->
  match unfold t with
  | Patt _ -> assert false
  | TEnv _ -> assert false
  | Kind -> assert false
  | Wild -> assert false
  | TRef _ -> assert false
  | Type -> (mk_Type, mk_Kind)
  | Vari x ->
      let a = try Ctxt.type_of x c with Not_found -> assert false in
      (t, a)
  | Symb s -> (t, !(s.sym_type))
  (* All metavariables inserted are typed. *)
  | (Meta (m, ts)) as t ->
      let rec ref_esubst i range =
        (* Refine terms of the explicit substitution. *)
        if i >= Array.length ts then range else
          match unfold range with
          | Prod(ai, b) ->
              ts.(i) <- force pb c ts.(i) ai;
              let b = Bindlib.subst b ts.(i) in
              ref_esubst (i + 1) b
          | _ ->
              (* Meta type must be a product of arity greater or equal
                 to the environment *)
              assert false
      in
      let range = ref_esubst 0 !(m.meta_type) in
      (t, range)
  | LLet (t_ty, t, u) ->
      (* Check that [a] is a type, and refine it. *)
      let t_ty, _ = type_enforce pb c t_ty in
      (* Check that [t] is of type [t_ty], and refine it *)
      let t = force pb c t t_ty in
      (* Unbind [u] and get new context with [x: t_ty ≔ t] *)
      let x, u, c = Ctxt.unbind c t_ty (Some t) u in
      (* Infer type of [u'] and refine it. *)
      let u, u_ty = infer pb c u in
      ( match unfold u_ty with
        | Kind ->
            Error.fatal_msg "Let bindings cannot have a body of type Kind.";
            Error.fatal_msg "Body of let binding [%a] has type Kind."
              Print.pp_term u;
            raise NotTypable
        | _ -> () );
      let u_ty = Bindlib.(u_ty |> lift |> bind_var x |> unbox) in
      let u = Bindlib.(u |> lift |> bind_var x |> unbox) in
      (mk_LLet (t_ty, t, u), mk_LLet(t_ty, t, u_ty))
  | Abst (dom, b) ->
      (* Domain must by of type Type (and not Kind) *)
      let dom = force pb c dom mk_Type in
      let x, b, c = Ctxt.unbind c dom None b in
      let b, range = infer pb c b in
      let b = Bindlib.(lift b |> bind_var x |> unbox) in
      let range = Bindlib.(lift range |> bind_var x |> unbox) in
      (mk_Abst (dom, b), mk_Prod (dom, range))
  | Prod (dom, b) ->
      (* Domain must by of type Type (and not Kind) *)
      let dom = force pb c dom mk_Type in
      let x, b, c = Ctxt.unbind c dom None b in
      let b, b_s = type_enforce pb c b in
      let b = Bindlib.(lift b |> bind_var x |> unbox) in
      (mk_Prod (dom, b), b_s)
  | Appl (t, u) -> (
      let t, t_ty = infer pb c t in
      match Eval.whnf c t_ty with
      | Prod (dom, b) ->
          if Logger.log_enabled () then log "Appl-prod arg [%a]" Print.pp_term u;
          let u = force pb c u dom in
          (mk_Appl (t, u), Bindlib.subst b u)
      | Meta (_, _) ->
          let u, u_ty = infer pb c u in
          let range = LibMeta.make_codomain pb c u_ty in
          unif pb c t_ty (mk_Prod (u_ty, range));
          (mk_Appl (t, u), Bindlib.subst range u)
      | t_ty ->
          let domain = LibMeta.make pb c mk_Type in
          let range = LibMeta.make_codomain pb c domain in
          let t = coerce pb c t t_ty (mk_Prod (domain, range)) in
          if Logger.log_enabled () then log "Appl-default arg [%a]" Print.pp_term u;
          let u = force pb c u domain in
          (mk_Appl (t, u), Bindlib.subst range u) )

and infer : problem -> ctxt -> term -> term * term = fun pb c t ->
  if Logger.log_enabled () then log "Infer [%a]" Print.pp_term t;
  let t, t_ty = infer_aux pb c t in
  if Logger.log_enabled () then
    log "Inferred [%a: %a]" Print.pp_term t Print.pp_term t_ty;
  (t, t_ty)


(** [noexn f cs c args] initialises {!val:constraints} to [cs],
    calls [f c args] and returns [Some(r,cs)] where [r] is the value of
    the call to [f] and [cs] is the list of constraints gathered by
    [f]. Function [f] may raise [NotTypable], in which case [None] is
    returned. *)
let noexn : (problem -> ctxt -> 'a -> 'b) -> problem -> ctxt -> 'a ->
  'b option =
  fun f pb c args ->
  try
    Some (f pb c args)
  with NotTypable -> None

let infer_noexn pb c t =
  if Logger.log_enabled () then
    log "Top infer %a%a" Print.pp_ctxt c Print.pp_term t;
  noexn infer pb c t

let check_noexn pb c t a =
  if Logger.log_enabled () then log "Top check \"%a\"" Print.pp_typing
      (c, t, a);
  let force pb c (t, a) = force pb c t a in
  noexn force pb c (t, a)

let check_sort_noexn pb c t : (term * term) option =
  if Logger.log_enabled () then
    log "Top check sort %a%a" Print.pp_ctxt c Print.pp_term t;
  noexn type_enforce pb c t

let infer_noexn pb c t = Option.map snd (infer_noexn pb c t)
let check_noexn pb c t a = check_noexn pb c t a <> None
let check_sort_noexn pb c t = check_sort_noexn pb c t <> None
