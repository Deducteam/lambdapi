(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console
open Eval

(** [unbind_tbinder c t f] returns [(x,u,c')] where [(x,u)] is the
    result of unbinding [f], and [c'] the extension of [c] with [x]
    mapped to [t]. *)
let unbind_tbinder (c:ctxt) (t:term) (f:tbinder) : tvar * term * ctxt =
  let x,u = Bindlib.unbind mkfree f in
  let c = if Bindlib.binder_occur f then add_tvar x t c else c in
  x,u,c

(** [unbind_tbinder2 c t f g] returns [(x,u,v,c')] where [(x,u,v)] is
    the result of unbinding [f] and [g], and [c'] the extension of [c]
    with [x] mapped to [t]. *)
let unbind_tbinder2 (c:ctxt) (t:term) (f:tbinder) (g:tbinder)
    : tvar * term * term * ctxt =
  let x,u,v = Bindlib.unbind2 mkfree f g in
  let c =
    if Bindlib.binder_occur f || Bindlib.binder_occur g
    then add_tvar x t c else c in
  x,u,v,c

(** [equal_vari t u] checks that [t] and [u] are the same variable. *)
let equal_vari (t:term) (u:term) : bool =
  match t, u with
  | Vari x, Vari y -> Bindlib.eq_vars x y
  | _, _ -> false

(** Constraints. *)
type problem = ctxt * term * term
let constraints : problem list ref = ref []

let with_constraints : ('a -> 'b) -> 'a -> problem list * 'b = fun fn e ->
  try
    constraints := [];
    let r = fn e in
    let cs = !constraints in
    constraints := [];
    (cs, r)
  with e -> constraints := []; raise e

(** [add_constr c t1 t2] extends [!constraints] with possibly new constraints
    for [t1] to be convertible to [t2] in context [c]. We assume that,
    for every [i], either [ti] is [Kind] or [ti] is typable. *)
let rec add_constr (c:ctxt) (t1:term) (t2:term) : unit =
  if !debug_unif then log "unif" "[%a] [%a]" pp t1 pp t2;
  match unfold t1, unfold t2 with
  | Type, Type
  | Kind, Kind -> ()

  | Vari x, Vari y when Bindlib.eq_vars x y -> ()

  | Prod(a,f), Prod(b,g)
  | Abst(a,f), Abst(b,g) ->
     add_constr c a b;
     let _,u,v,c' = unbind_tbinder2 c a f g in
     add_constr c' u v

  | Symb(s1), Symb(s2) when s1 == s2 -> ()

  | Meta(m1,a1), Meta(m2,a2) when m1==m2 && Array.for_all2 equal_vari a1 a2 ->
     ()

  | Meta(m,ts), _ when distinct_vars ts && not (occurs m t2) ->
     instantiate m ts t2

  | _, Meta(m,ts) when distinct_vars ts && not (occurs m t1) ->
     instantiate m ts t1

  | Meta(_,_), _
  | _, Meta(_,_) -> raw_add_constr c t1 t2

  | Symb(_), _
  | _, Symb(_)
  | Appl(_,_), _
  | _, Appl(_,_) ->
     if not (Terms.eq t1 t2) then add_constr_whnf c (whnf t1) (whnf t2)

  | _, _ -> fatal "[%a] and [%a] are not convertible\n" pp t1 pp t2

(** [add_constr_whnf c t1 t2] extends [!constraints] with possibly new
    constraints for [t1] to be convertible to [t2] in context [c]. We
    assume that, for every [i], either [ti] is [Kind] or [ti] is
    typable. We also assume that [t1] and [t2] are in whnf. *)
and add_constr_whnf (c:ctxt) (t1:term) (t2:term) : unit =
  let h1, ts1 = get_args t1 and h2, ts2 = get_args t2 in
  let n1 = List.length ts1 and n2 = List.length ts2 in
  match h1, h2 with
  | Type, Type
  | Kind, Kind -> ()
     (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)

  | Vari x, Vari y when Bindlib.eq_vars x y && n1 = n2 ->
     add_constr_args c ts1 ts2

  | Prod(a,f), Prod(b,g)
     (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)
  | Abst(a,f), Abst(b,g) ->
     (* We have [ts1=ts2=[]] since [t1] and [t2] are in whnf. *)
     add_constr c a b;
     let _,u,v,c' = unbind_tbinder2 c a f g in
     add_constr c' u v

  | Symb(s1), Symb(s2) when s1.sym_rules = [] && s2.sym_rules = [] ->
     if s1 == s2 && n1 = n2 then add_constr_args c ts1 ts2
     else fatal "[%a] and [%a] are not convertible\n" pp h1 pp h2

  | Symb(s1), Symb(s2) when s1==s2 && n1 = 0 && n2 = 0 -> ()

  | Meta(m1,a1), Meta(m2,a2)
    when m1==m2 && Array.for_all2 equal_vari a1 a2 && n1 = 0 && n2 = 0 -> ()

  | Meta(m,ts), _ when n1 = 0 && distinct_vars ts && not (occurs m t2) ->
     instantiate m ts t2

  | _, Meta(m,ts) when n2 = 0 && distinct_vars ts && not (occurs m t1) ->
     instantiate m ts t1

  | Meta(_,_), _
  | _, Meta(_,_) -> raw_add_constr c t1 t2

  | Symb(_), _
  | _, Symb(_) ->
     if not (eq_modulo t1 t2) then raw_add_constr c t1 t2
  (*FIXME? detect whether [t1] or [t2] can be reduced after instantiation*)

  | _, _ -> fatal "[%a] and [%a] are not convertible\n" pp t1 pp t2

and raw_add_constr c t1 t2 =
  if !debug_unif then log "raw_add_constr" "[%a] ~ [%a]" pp t1 pp t2;
  constraints := (c,t1,t2)::!constraints

(** Instantiate [m[t1,..,tn]] by [v], and recompute [!constraints]. We
    assume that [t1,..,tn] are distinct variables and that [m] does
    not occur in [v]. Fails if [v] contains free variables distinct
    from [t1,..,tn]. *)
and instantiate (m:meta) (ts:term array) (v:term) : unit =
  let xs = Array.map to_var ts in
  let bv = Bindlib.bind_mvar xs (lift v) in
  (*FIXME:if Bindlib.is_closed bv then
    begin
      Unif.set_meta m (Bindlib.unbox bv);
      recompute_constraints()
    end
  else
    fatal "cannot instantiate %a[%a] by [%a]"
    pp_meta m (Array.pp pp ",") ts pp v*)
  Unif.set_meta m (Bindlib.unbox bv);
  recompute_constraints()

(** [recompute_constraints p] iterates [add_constr] on [p]. *)
and recompute_constraints() : unit =
  let cs = !constraints in
  constraints := [];
  List.iter (fun (c,a,b) -> add_constr c a b) cs

(** [add_constr_args c ts1 ts2 p] extends [p] with possibly new
    constraints for the terms of [ts1] and [ts2] to be pairwise
    convertible in context [c]. [ts1] and [ts2] must have the same
    length. *)
and add_constr_args (c:ctxt) (ts1:term list) (ts2:term list) : unit =
  List.iter2 (fun a b -> add_constr c a b) ts1 ts2

(** [create_meta c] creates a term [m[x1,,,xn]] where [m] is a new
    metavariable and [x1,..,xn] are the variables of [c]. *)
let create_meta (c:ctxt) : term =
  let typ_m = prod_ctxt c Type in
  let m = new_meta typ_m (List.length c) in
  let vs = List.rev_map (fun (x,_) -> Vari x) c in
  Meta(m, Array.of_list vs)

(** [to_prod r e xo] instantiates the metavariable [r] (with [e] as an
    environment) using a product type formed with fresh metavariables.
    The argument [xo] is used to name the bound variable. Note that the binder
    (the body) is constant if [xo] is equal to [None]. *)
let to_prod m ts so =
  let m1 = new_meta Type 0 in (*FIXME*)
  let m2 = new_meta Type 0 in (*FIXME*)
  let bts = Array.map lift ts in
  let a = _Meta m1 bts in
  let f x = _Meta m2 (Array.append bts [|_Vari x|]) in
  let s = match so with Some s -> s | None -> "x" in
  let p = Bindlib.unbox (_Prod a s f) in
  instantiate m ts p

(** [infer c t] returns a type for [t] in [c]. *)
let rec infer (c:ctxt) (t:term) : term =
  let m_vs = create_meta c in
  check c t m_vs;
  m_vs

(** [check c t a] checks that [t] is of type [a] in [c]. [a] must be
    [Kind] or be typable by a sort. *)
and check (c:ctxt) (t:term) (a:term) : unit =
  if !debug_type then log "check" "[%a] [%a]" pp t pp a;
  match unfold t with
  | Patt(_,_,_) | TEnv(_,_) | Kind -> assert false

  | Type -> add_constr c a Kind

  | Vari(x) ->
     let typ_x = try find_tvar x c with Not_found -> assert false in
     add_constr c a typ_x

  | Symb(s) -> add_constr c a s.sym_type

  | Prod(t,f) ->
     begin
       check c t Type;
       let _,u,c' = unbind_tbinder c t f in
       check c' u a;
       match unfold a with
       | Type | Kind -> ()
       | _ -> fatal "[%a] is not a sort\n" pp a
     end

  | Abst(t,f) ->
     begin
       check c t Type;
       let a = whnf a in
       begin
         match a with
         | Meta(m,ts) when distinct_vars ts ->
            to_prod m ts (Some(Bindlib.binder_name f))
         | _ -> ()
       end;
       match unfold a with
       | Prod(b,g) ->
          begin
            add_constr c b t;
            let _,u,d,c' = unbind_tbinder2 c t f g in
            check c' u d
          end
       | _ -> fatal "[%a] is not a product\n" pp a
     end

  | Appl(t,u) ->
     begin
       let typ_t = infer c t in
       let typ_t = whnf typ_t in
       begin
         match typ_t with
         | Meta(m,ts) when distinct_vars ts -> to_prod m ts None
         | _ -> ()
       end;
       match unfold typ_t with
       | Prod(b,g) -> check c u b; add_constr c a (Bindlib.subst g u)
       | _ -> fatal "[%a] is not a product\n" pp typ_t
     end

  | Meta(m, ts) ->
     (* The type of [Meta(m,ts)] is the same as [add_args v ts]
        where [v] is some fresh variable with the same type as [m]. *)
     begin
       let v = Bindlib.new_var mkfree (meta_name m) in
       let c' = add_tvar v m.meta_type c in
       check c' (add_args (Vari v) (Array.to_list ts)) a
     end

(** Solve constraints. *)
let solve : problem list -> bool = fun cs ->
  let msg (_,a,b) = wrn "Cannot solve constraint [%a] ~ [%a]\n" pp a pp b in
  List.iter msg cs; cs = []

(** [has_type c t u] returns [true] iff [t] has type [u] in context [c]. *)
let has_type : ctxt -> term -> term -> bool = fun ctxt t a ->
  let (cs, r) = with_constraints (check ctxt t) a in
  solve cs

(** [sort_type c t] returns [true] iff [t] has type a sort in context [c]. *)
let sort_type : ctxt -> term -> term = fun ctx a ->
  let (cs, s) = with_constraints (infer ctx) a in
  if not (solve cs) then fatal "Constraints cannot be solved.\n";
  match unfold s with
  | Type
  | Kind -> s
  | _    -> fatal "[%a] has type [%a] (not a sort)...\n" pp a pp s

(** If [infer c t] returns [Some u], then [t] has type [u] in context
    [c]. If it returns [None] then some constraints could not be solved. *)
let infer : ctxt -> term -> term option = fun ctx t ->
  let (cs, a) = with_constraints (infer ctx) t in
  if not (solve cs) then None else Some(a)
