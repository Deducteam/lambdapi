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

(** Given a meta [m] of type [Πx1:a1,..,Πxn:an,b], [set_to_prod d p m] sets
   [m] to a product term of the form [Πy:m1[x1;..;xn],m2[x1;..;xn;y]] with
   [m1] and [m2] fresh metavariables, and adds these metavariables to [p].
   [d] is the call depth used for debug. *)
let set_to_prod : int -> problem -> meta -> unit = fun d p m ->
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
  if !log_enabled then
    log_infr (red "%a%a ≔ %a") D.depth d pp_meta m pp_term (Bindlib.unbox r);
  LibMeta.set p m (Bindlib.unbox (Bindlib.bind_mvar vs r))

(** [conv d p c a b] adds the the constraint [(c,a,b)] in [p], if [a] and
   [b] are not convertible. [d] is the call depth used for debug. *)
let conv : int -> problem -> ctxt -> term -> term -> unit = fun d p c a b ->
  if not (Eval.eq_modulo c a b) then
    (let cstr = (c,a,b) in
     p := {!p with to_solve = cstr::!p.to_solve};
     if !log_enabled then log_infr (mag "%aadd %a") D.depth d pp_constr cstr)

(** Exception that may be raised by type inference. *)
exception NotTypable

(** [infer d p c t] tries to infer a type for the term [t] in context [c],
   possibly adding new unification constraints in [p]. The set of
   metavariables of [p] are updated if some metavariables are instantiated or
   created. The returned type is well-sorted if the recorded constraints are
   satisfied. [c] must be well sorted. [d] is the call depth used for debug.
@raise NotTypable when the term is not typable (when encountering an
   abstraction over a kind). *)
let rec infer : int -> problem -> ctxt -> term -> term = fun d p c t ->
  let return v =
    if !log_enabled then log_infr "%a%a" D.depth d pp_term v; v in
  if !log_enabled then log_infr "%ainfer %a%a" D.depth d pp_ctxt c pp_term t;
  match unfold t with
  | Patt(_,_,_) -> assert false (* Forbidden case. *)
  | TEnv(_,_)   -> assert false (* Forbidden case. *)
  | Kind        -> assert false (* Forbidden case. *)
  | Wild        -> assert false (* Forbidden case. *)
  | TRef(_)     -> assert false (* Forbidden case. *)

  (* -------------------
      c ⊢ Type ⇒ Kind  *)
  | Type -> return mk_Kind

  (* ---------------------------------
      c ⊢ Vari x ⇒ Ctxt.type_of x c  *)
  | Vari x -> (try return (Ctxt.type_of x c) with Not_found -> assert false)

  (* -------------------------------
      c ⊢ Symb s ⇒ !(s.sym_type)  *)
  | Symb s -> return !(s.sym_type)

  (*  c ⊢ a ⇐ Type    c, x:a ⊢ b ⇒ s in {Type,Kind}
     -----------------------------------------
                c ⊢ Prod(a,b) ⇒ s            *)
  | Prod(a,b) ->
      check (d+1) p c a mk_Type;
      let _,b,c' = Ctxt.unbind c a None b in
      let s = infer (d+1) p c' b in
      begin match unfold s with
      | (Type | Kind) as s -> s
      | _ -> conv d p c' s mk_Type; mk_Type
      (* Here, we force [s] to be equivalent to [Type] as there is little
         (no?) chance that it can be a kind. *)
      end

  (*  c ⊢ a ⇐ Type    c, x:a ⊢ t ⇒ b   b ≠ Kind
     --------------------------------------------
             c ⊢ Abst(a,t) ⇒ Prod(a,b)          *)
  | Abst(a,t) ->
      check (d+1) p c a mk_Type;
      let x,t,c' = Ctxt.unbind c a None t in
      let b = infer (d+1) p c' t in
      begin match unfold b with
      | Kind ->
          wrn None "Abstraction on [%a] is not allowed." Print.pp_term t;
          raise NotTypable
      | _ -> return (mk_Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b))))
      end

  (*  c ⊢ t ⇒ Prod(a,b)    c ⊢ u ⇐ a
     ------------------------------------
         c ⊢ Appl(t,u) ⇒ subst b u      *)
  | Appl(t,u) ->
      (* [get_prod f typ] returns the domain and codomain of [t] if [t] is a
         product. If [t] is a metavariable, then it instantiates it with a
         product and calls [get_prod f typ] again. Otherwise, it calls [f
         typ]. *)
      let rec get_prod f typ =
        match unfold typ with
        | Prod(a,b) -> (a,b)
        | Meta(m,_) -> set_to_prod d p m; get_prod f typ
        | _ -> f typ
      in
      let get_prod_whnf = (* assumes that its argument is in whnf *)
        get_prod (fun typ ->
            let a = LibMeta.make p c mk_Type in
            (* We force [b] to be of type [Type] as there is little (no?)
               chance that it can be a kind. *)
            let b = LibMeta.make_codomain p c a in
            conv d p c typ (mk_Prod(a,b)); (a,b)) in
      let get_prod =
        get_prod (fun typ -> get_prod_whnf (Eval.whnf c typ)) in
      let a, b = get_prod (infer (d+1) p c t) in
      check (d+1) p c u a;
      return (Bindlib.subst b u)

  (* c ⊢ t ⇐ a   c, x:a ≔ t ⊢ u ⇒ b   c, x:a ≔ t ⊢ b : s in {Type,Kind}
     ------------------------------------------------------------------
        c ⊢ let x:a ≔ t in u ⇒ let x:a ≔ t in b

     See Pure type systems with definitions, P. Severi and E. Poll,
     LFCS 1994, http://doi.org/10.1007/3-540-58140-5_30. *)
  | LLet(a,t,u) ->
      check (d+1) p c a mk_Type;
      check (d+1) p c t a;
      let x,u,c' = Ctxt.unbind c a (Some t) u in
      let b = infer (d+1) p c' u in
      begin match unfold b with
      | Kind ->
          wrn None "Abstraction on [%a] is not allowed." Print.pp_term u;
          raise NotTypable
      | _ ->
          let s = infer (d+1) p c' b in
          begin match unfold s with
          | Type | Kind -> ()
          | _ -> conv d p c' s mk_Type
          (* Here, we force [s] to be equivalent to [Type] as there is little
             (no?) chance that it can be a kind. *)
          end;
          let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
          return (mk_LLet(a,t,b))
      end

  (*  c ⊢ term_of_meta m ts ⇒ a
     ----------------------------
         c ⊢ Meta(m,ts) ⇒ a      *)
  | Meta(m,ts) ->
      (* The type of [Meta(m,ts)] is the same as the one obtained by applying
         to [ts] a new symbol having the same type as [m]. *)
      let s = Term.create_sym (Sign.current_path()) Privat Const
          Eager true ("?" ^ LibMeta.name m) !(m.meta_type) [] in
      if !log_enabled then
        log_infr "%areplace meta by fresh symbol" D.depth d;
      infer d p c
        (Array.fold_left (fun acc t -> mk_Appl(acc,t)) (mk_Symb s) ts)

(** [check d c t a] checks that the term [t] has type [a] in context [c],
   possibly adding new unification constraints in [p]. [c] must be
   well-formed and [a] well-sorted. [d] is the call depth used for debug.
@raise NotTypable when the term is not typable (when encountering an
   abstraction over a kind). *)
and check : int -> problem -> ctxt -> term -> term -> unit = fun d p c t a ->
  if !log_enabled then log_infr "%acheck %a" D.depth d pp_typing (c,t,a);
  conv d p c (infer (d+1) p c t) a

(** [infer_noexn p c t] returns [None] if the type of [t] in context [c]
   cannot be inferred, or [Some a] where [a] is some type of [t] in the
   context [c], possibly adding new constraints in [p]. The metavariables of
   [p] are updated when a metavariable is instantiated or created. [c] must
   be well sorted. *)
let infer_noexn : problem -> ctxt -> term -> term option = fun p c t ->
  try
    if !log_enabled then
      log_hndl (blu "infer_noexn %a%a") pp_ctxt c pp_term t;
    let a = time_of (fun () -> infer 0 p c t) in
    if !log_enabled then
      log_hndl (blu "result of infer_noexn: %a%a")
        pp_term a pp_constrs !p.to_solve;
    Some a
  with NotTypable -> None

(** [check_noexn p c t a] tells whether the term [t] has type [a] in the
   context [c], possibly adding new constraints in |p]. The metavariables of
   [p] are updated when a metavariable is instantiated or created. The context
   [c] and the type [a] must be well sorted. *)
let check_noexn : problem -> ctxt -> term -> term -> bool = fun p c t a ->
  try
    if !log_enabled then log_hndl (blu "check_noexn %a") pp_typing (c,t,a);
    time_of (fun () -> check 0 p c t a);
    if !log_enabled && !p.to_solve <> [] then
      log_hndl (blu "result of check_noexn:%a") pp_constrs !p.to_solve;
    true
  with NotTypable -> false

let set_to_prod = set_to_prod 0
