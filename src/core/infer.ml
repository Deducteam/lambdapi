(** Type inference and checking *)

open Common
open Lplib
open Term
open Timed

(** Logging function for typing. *)
let log = Logger.make 'i' "infr" "type inference/checking"
let log = log.pp

(* Optimised context *)
type octxt = ctxt * bctxt
let boxed = snd
let classic = fst
let extend (cctx, bctx) v ?def ty =
  ((v, ty, def) :: cctx, if def <> None then bctx else (v, lift ty) :: bctx)

let unbox = Bindlib.unbox

(** Exception that may be raised by type inference. *)
exception NotTypable

(** [unif pb c a b] solves the unification problem [c ⊢ a ≡ b]. Current
    implementation collects constraints in {!val:constraints} then solves
    them at the end of type checking. *)
let unif : problem -> octxt -> term -> term -> unit =
 fun pb c a b ->
 if not (Eval.pure_eq_modulo (classic c) a b) then
 (* NOTE: eq_modulo is used because the unification algorithm counts on
    the fact that no constraint is added in some cases (see test
    "245b.lp"). We may however want to reduce the number of calls to
    [eq_modulo]. *)
   begin
     if Logger.log_enabled () then
       log (Color.yel "add constraint %a") Print.pp_constr
         (classic c, a, b);
     pb := {!pb with to_solve = (classic c, a, b) :: !pb.to_solve}
   end

(** {1 Handling coercions} *)

(** [is_value t] is true if term [t] does not contain [Coercions.coerce]. *)
let is_value t =
  let exception Found in
  (* TODO: write a generic [iter] that operates on leaves *)
  let rec is_value t =
    match unfold t with
    | TRef _ -> assert false
    | TEnv _ -> assert false
    | Wild -> assert false
    | Patt _ -> assert false
    | Plac _ -> assert false
    | Type | Kind | Vari _ | Meta _ -> ()
    | Symb s -> if Coercions.is_ghost s then raise Found
    | Appl(t,u) -> is_value t; is_value u
    | Prod(a,b)
    | Abst(a,b) -> is_value a; is_value (snd (Bindlib.unbind b))
    | LLet(a,t,u) -> is_value a; is_value t; is_value (snd (Bindlib.unbind u))
  in
  try is_value t; true with Found -> false

(* Simply unify types, no coercions yet. *)
let coerce pb c t a b = 
  if Logger.log_enabled () then log "Coerce [%a: %a = %a]"
    Print.pp_term t Print.pp_term a Print.pp_term b;
  let reduced = 
    add_args (mk_Symb Coercions.coerce) [a; t; b]
    |> Eval.snf (classic c)
  in
  if is_value reduced then (reduced, true) else (
    unif pb c a b; (t, false))

(** {1 Other rules} *)

(** NOTE: functions {!val:type_enforce}, {!val:force} and {!val:infer}
    return a boolean which is true iff the typechecked term has been
    modified. It allows to bypass reconstruction of some Bindlib terms (which
    call [lift |> bind_var x |> unbox]). It reduces the type checking time of
    Holide by 21%. *)

(** [type_enforce pb c a] returns a tuple [(a',s)] where [a'] is refined
    term [a] and [s] is a sort (Type or Kind) such that [a'] is of type
    [s]. *)
let rec type_enforce : problem -> octxt -> term -> term * term * bool =
 fun pb c a ->
  if Logger.log_enabled () then log "Type enforce [%a]" Print.pp_term a;
  let a, s, cui = infer pb c a in
  let sort =
    match unfold s with
    | Kind -> mk_Kind
    | Type -> mk_Type
    | _ -> mk_Type
    (* FIXME The algorithm should be able to backtrack on the choice of
       this sort, first trying [Type], and if it does not succeed, trying
       [Kind]. *)
  in
  let a, cu = coerce pb c a s sort in
  (a, sort, cui || cu)

(** [force pb c t a] returns a term [t'] such that [t'] has type [a],
    and [t'] is the refinement of [t]. *)
and force : problem -> octxt -> term -> term -> term * bool =
 fun pb c te ty ->
 if Logger.log_enabled () then
   log "Force [%a] of [%a]" Print.pp_term te Print.pp_term ty;
 match unfold te with
 | Plac (true, name) ->
     unif pb c ty mk_Type;
     (unbox (LibMeta.bmake pb ?name (boxed c) _Type), true)
 | Plac (false, name) ->
     (unbox (LibMeta.bmake pb ?name (boxed c) (lift ty)), true)
 | _ ->
     let (t, a, cui) = infer pb c te in
     let t, cu = coerce pb c t a ty in
     (t, cu || cui)

and infer_aux : problem -> octxt -> term -> term * term * bool =
 fun pb c t ->
  match unfold t with
  | Patt _ -> assert false
  | TEnv _ -> assert false
  | Kind -> assert false
  | Wild -> assert false
  | TRef _ -> assert false
  | Type -> (mk_Type, mk_Kind, false)
  | Vari x ->
      let a = try Ctxt.type_of x (classic c) with Not_found -> assert false in
      (t, a, false)
  | Symb s -> (t, !(s.sym_type), false)
  | Plac (true, name) ->
      let m = LibMeta.bmake pb ?name (boxed c) _Type in
      (unbox m, mk_Type, true)
  | Plac (false, name) ->
      let mt = LibMeta.bmake pb (boxed c) _Type in
      let m = LibMeta.bmake pb ?name (boxed c) mt in
      (unbox m, unbox mt, true)
  (* All metavariables inserted are typed. *)
  | (Meta (m, ts)) as t ->
      let cu = Stdlib.ref false in
      let rec ref_esubst i range =
        (* Refine terms of the explicit substitution. *)
        if i >= Array.length ts then range else
          match unfold range with
          | Prod(ai, b) ->
              let (tsi, cuf) = force pb c ts.(i) ai in
              ts.(i) <- tsi;
              Stdlib.(cu := !cu || cuf);
              let b = Bindlib.subst b ts.(i) in
              ref_esubst (i + 1) b
          | _ ->
              (* Meta type must be a product of arity greater or equal
                 to the environment *)
              assert false
      in
      let range = ref_esubst 0 !(m.meta_type) in
      (t, range, Stdlib.(!cu))
  | LLet (t_ty, t, u) as top ->
      (* Check that [a] is a type, and refine it. *)
      let t_ty, _, cu_t_ty = type_enforce pb c t_ty in
      (* Check that [t] is of type [t_ty], and refine it *)
      let t, cu_t = force pb c t t_ty in
      (* Unbind [u] and get new context with [x: t_ty ≔ t] *)
      let (x, u) = Bindlib.unbind u in
      let c = extend c x ~def:t t_ty in
      (* Infer type of [u'] and refine it. *)
      let u, u_ty, cu_u = infer pb c u in
      ( match unfold u_ty with
        | Kind ->
            Error.fatal_msg "Let bindings cannot have a body of type Kind.";
            Error.fatal_msg "Body of let binding [%a] has type Kind."
              Print.pp_term u;
            raise NotTypable
        | _ -> () );
      let u_ty = Bindlib.(u_ty |> lift |> bind_var x |> unbox) in
      let top_ty = mk_LLet (t_ty, t, u_ty) in
      let cu = cu_t_ty || cu_t || cu_u in
      let top =
        if cu then
          let u = Bindlib.(u |> lift |> bind_var x |> unbox) in
          mk_LLet(t_ty, t, u)
        else top
      in
      (top, top_ty, cu)
  | Abst (dom, b) as top ->
      (* Domain must by of type Type (and not Kind) *)
      let dom, cu_dom = force pb c dom mk_Type in
      let (x, b) = Bindlib.unbind b in
      let c = extend c x dom in
      let b, range, cu_b = infer pb c b in
      let range = Bindlib.(lift range |> bind_var x |> unbox) in
      let top_ty = mk_Prod (dom, range) in
      let cu = cu_b || cu_dom in
      let top =
        if cu then
          let b = Bindlib.(lift b |> bind_var x |> unbox) in
          mk_Abst (dom, b)
        else top
      in
      (top, top_ty, cu)
  | Prod (dom, b) as top ->
      (* Domain must by of type Type (and not Kind) *)
      let dom, cu_dom = force pb c dom mk_Type in
      let (x, b) = Bindlib.unbind b in
      let c = extend c x dom in
      let b, b_s, cu_b = type_enforce pb c b in
      let cu = cu_b || cu_dom in
      let top =
        if cu then
          let b = Bindlib.(lift b |> bind_var x |> unbox) in
          mk_Prod (dom, b)
        else top
      in
      (top, b_s, cu)
  | Appl (t, u) as top -> (
      let t, t_ty, cu_t = infer pb c t in
      let return m t u range =
        let ty = Bindlib.subst range u and cu = cu_t || m in
        if cu then (mk_Appl (t, u), ty, cu) else (top, ty, cu)
      in
      match Eval.whnf (classic c) t_ty with
      | Prod (dom, range) ->
          if Logger.log_enabled () then log "Appl-prod arg [%a]" Print.pp_term u;
          let u, cu_u = force pb c u dom in
          return cu_u t u range
      | Meta (_, _) ->
          let u, u_ty, cu_u = infer pb c u in
          let range =
            unbox (LibMeta.bmake_codomain pb (boxed c) (lift u_ty))
          in
          unif pb c t_ty (mk_Prod (u_ty, range));
          return cu_u t u range
      | t_ty ->
          let domain = LibMeta.bmake pb (boxed c) _Type in
          let range = LibMeta.bmake_codomain pb (boxed c) domain in
          let domain = unbox domain
          and range = unbox range in
          let t, cu_t' = coerce pb c t t_ty (mk_Prod (domain, range)) in
          if Logger.log_enabled () then log "Appl-default arg [%a]" Print.pp_term u;
          let u, cu_u = force pb c u domain in
          return (cu_t' || cu_u) t u range )


and infer : problem -> octxt -> term -> term * term * bool = fun pb c t ->
  if Logger.log_enabled () then log "Infer [%a]" Print.pp_term t;
  let t, t_ty, cu = infer_aux pb c t in
  if Logger.log_enabled () then
    log "Inferred [%a:@ %a]" Print.pp_term t Print.pp_term t_ty;
  (t, t_ty, cu)

(** {b NOTE} when unbinding a binder [b] (e.g. when inferring the type of an
    abstraction [λ x, e]) in context [c], [c] is always extended, even if
    binder [b] is constant. This is because during typechecking, the context
    must contain all variables traversed to build appropriate meta-variables.
    Otherwise, the term [λ a: ?*, λ b: ?*, b] will be transformed to [λ _: ?1,
    λ b: ?2, b] whereas it should be [λ a: ?1, λ b: ?2[a], b] *)

(** [noexn f cs c args] initialises {!val:constraints} to [cs],
    calls [f c args] and returns [Some(r,cs)] where [r] is the value of
    the call to [f] and [cs] is the list of constraints gathered by
    [f]. Function [f] may raise [NotTypable], in which case [None] is
    returned. *)
let noexn : (problem -> octxt -> 'a -> 'b) -> problem -> ctxt -> 'a ->
  'b option =
  fun f pb c args ->
  try
    Some (f pb (c, Ctxt.box_context c) args)
  with NotTypable -> None

let infer_noexn pb c t : (term * term) option =
  if Logger.log_enabled () then
    log "Top infer %a%a" Print.pp_ctxt c Print.pp_term t;
  let infer pb c t = let (t,t_ty,_) = infer pb c t in (t, t_ty) in
  noexn infer pb c t

let check_noexn pb c t a : term option =
  if Logger.log_enabled () then log "Top check \"%a\"" Print.pp_typing
      (c, t, a);
  let force pb c (t, a) = fst (force pb c t a) in
  noexn force pb c (t, a)

let check_sort_noexn pb c t : (term * term) option =
  if Logger.log_enabled () then
    log "Top check sort %a%a" Print.pp_ctxt c Print.pp_term t;
  let type_enforce pb c t = let (t, s, _) = type_enforce pb c t in (t, s) in
  noexn type_enforce pb c t
