(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console
open Eval

(** [prod x t u] creates the dependent product of [t] and [u] by
    binding [x] in [u]. *)
let prod (x:tvar) (t:term) (u:term) : term =
  Prod(t, Bindlib.unbox (Bindlib.bind_var x (lift u)))

(** [prod_ctxt c u] iterates [prod] over [c]. *)
let prod_ctxt (c:ctxt) (t:term) : term =
  List.fold_left (fun t (x,a) -> prod x a t) t c

(** Representation of a convertibility constraint between two terms in
    a context. *)
type constr = ctxt * term * term

let pp_constr : out_channel -> constr -> unit = fun oc (c,t,u) ->
  Printf.fprintf oc "%a ~ %a" pp t pp u

(** Representation of sets of constraints. *)
type problem = constr list

let pp_problem : out_channel -> problem -> unit = fun oc p ->
  if p = [] then output_string oc "∅"
  else Printf.fprintf oc "{%a}" (List.pp pp_constr ", ") p

(** [unbind_tbinder c t f] returns [(x,u,c')] where [(x,u)] is the
    result of unbinding [f], and [c'] the extension of [c] with [x]
    mapped to [t]. *)
let unbind_tbinder (c:ctxt) (t:term) (f:tbinder) : tvar * term * ctxt =
  let (x,u) = Bindlib.unbind mkfree f in
  let c = if Bindlib.binder_occur f then add_tvar x t c else c in
  x,u,c

(** [unbind_tbinder2 c t f g] returns [(x,u,v,c')] where [(x,u,v)] is
    the result of unbinding [f] and [g], and [c'] the extension of [c]
    with [x] mapped to [t]. *)
let unbind_tbinder2 (c:ctxt) (t:term) (f:tbinder) (g:tbinder)
    : tvar * term * term * ctxt =
  let (x,u,v) = Bindlib.unbind2 mkfree f g in
  let c =
    if Bindlib.binder_occur f || Bindlib.binder_occur g
    then add_tvar x t c else c in
  x,u,v,c

(** [equal_vari t u] checks that [t] and [u] are the same variable. *)
let equal_vari (t:term) (u:term) : bool =
  match t, u with
  | Vari x, Vari y -> Bindlib.eq_vars x y
  | _, _ -> false

(** [infer p c t] returns a pair [(p',u)] where [p'] extends [p] with
    possibly new constraints for [t] to be of type [u]. *)
let rec infer (p:problem) (c:ctxt) (t:term) : problem * term =
  if !debug_type then log "INFR" "%a; %a ⊢ %a" pp_problem p pp_ctxt c pp t;
  let p, typ_t =
    match unfold t with
    | Patt(_,_,_) | TEnv(_,_) | Kind -> assert false

    | Type        -> p, Kind

    | Vari(x)     ->
       begin try p, find_tvar x c with Not_found -> assert false end

    | Symb(s)     -> p, s.sym_type

    | Prod(t,f) ->
       begin
        let p = check p c t Type in
        let x,u,c = unbind_tbinder c t f in
        let p, typ_u = infer p c u in
        let typ_u = whnf typ_u in
        match typ_u with
        | Type | Kind -> p, typ_u
        | _ -> fatal "[%a] has type [%a] (not a sort)\n" pp u pp typ_u
       end

    | Abst(t,f) ->
       begin
        let p = check p c t Type in
        let x,u,c = unbind_tbinder c t f in
        let p, typ_u = infer p c u in
        p, prod x t typ_u
       end

    | Appl(t,u) ->
       let p, typ_u = infer p c u in
       let p, typ_t = infer p c t in
       (* We build the product type [a = x:typ_u -> m[x1,..,xn,x]] where [m]
          is a new metavariable. *)
       let x = Bindlib.new_var mkfree "x" in
       let c' = (x,typ_u)::c in
       let typ_m = prod_ctxt c' Type in
       let n = List.length c' in
       let m = new_meta typ_m n in
       let vs = List.rev_map (fun (x,_) -> Vari x) c' in
       let m_vs = Meta(m, Array.of_list vs) in
       let a = prod x typ_u m_vs in
       (* We add the constraint [a = typ_t]. *)
       let p = add_constr c a typ_t p in
       let typ =
         match a with
         | Prod(_,f) -> Bindlib.subst f u
         | _ -> assert false
       in
       p, typ

    | Meta(m, ts) ->
       (* The type of [Meta(m,ts)] is the same as [add_args v ts]
         where [v] is some fresh variable with the same type as [m]. *)
       begin
        let v = Bindlib.new_var mkfree (meta_name m) in
        let c = add_tvar v m.meta_type c in
        infer p c (add_args (Vari v) (Array.to_list ts))
       end
  in
  if !debug_type then
    log "INFR" (gre "%a; %a ⊢ %a : %a") pp_problem p pp_ctxt c pp t pp typ_t;
  p, typ_t

(** [check p c t u] extends [p] with possibly new constraints for [t]
    to be of type [u] in context [c]. *)
and check (p:problem) (c:ctxt) (t:term) (u:term) : problem =
  let p, typ_t = infer p c t in
  add_constr c typ_t u p

(** [add_constr c t1 t2 p] extends [p] with possibly new constraints
    for [t1] to be convertible to [t2] in context [c]. We assume that,
    for every [i], either [ti] is [Kind] or [ti] is typable. *)
and add_constr (c:ctxt) (t1:term) (t2:term) (p:problem) : problem =
  if !debug_unif then log "unif" "[%a] ~?~ [%a]" pp t1 pp t2;
  match unfold t1, unfold t2 with
  | Type, Type
  | Kind, Kind -> p

  | _, Kind
  | Kind, _ -> fatal "[%a] and [%a] are not convertible\n" pp t1 pp t2

  | Vari x, Vari y when Bindlib.eq_vars x y -> p

  | Prod(a,f), Prod(b,g)
  | Abst(a,f), Abst(b,g) ->
     let p = add_constr c a b p in
     let x,u,v,c' = unbind_tbinder2 c a f g in
     add_constr c' u v p

  | Symb(s1), Symb(s2) when s1 == s2 -> p

  | Meta(m1,a1), Meta(m2,a2) when m1==m2 && Array.for_all2 equal_vari a1 a2 -> p

  | Meta(m,a), _ when distinct_vars a && not (occurs m t2) ->
     let b = Array.map to_var a in
     Unif.set_meta m (Bindlib.unbox (Bindlib.bind_mvar b (lift t2)));
     recompute_constrs p

  | _, Meta(m,a) when distinct_vars a && not (occurs m t1) ->
     let b = Array.map to_var a in
     Unif.set_meta m (Bindlib.unbox (Bindlib.bind_mvar b (lift t1)));
     recompute_constrs p

  | Meta(_,_), _
  | _, Meta(_,_) -> raw_add_constr c t1 t2 p

  | Symb(_), _
  | _, Symb(_)
  | Appl(_,_), _
  | _, Appl(_,_) ->
     if Terms.eq t1 t2 then p else add_constr_whnf c (whnf t1) (whnf t2) p

  | _, _ -> fatal "[%a] and [%a] are not convertible\n" pp t1 pp t2

(** [add_constr_whnf c t1 t2 p] extends [p] with possibly new
    constraints for [t1] to be convertible to [t2] in context [c]. We
    assume that, for every [i], either [ti] is [Kind] or [ti] is
    typable. We also assume that [t1] and [t2] are in whnf. *)
and add_constr_whnf (c:ctxt) (t1:term) (t2:term) (p:problem) : problem =
  let h1, ts1 = get_args t1 and h2, ts2 = get_args t2 in
  let n1 = List.length ts1 and n2 = List.length ts2 in
  match h1, h2 with
  | Type, Type
  | Kind, Kind -> p
     (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)

  | _, Kind
  | Kind, _ -> fatal "[%a] and [%a] are not convertible\n" pp t1 pp t2

  | Vari x, Vari y when Bindlib.eq_vars x y && n1 = n2 ->
     add_constr_args c ts1 ts2 p

  | Prod(a,f), Prod(b,g)
     (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)
  | Abst(a,f), Abst(b,g) ->
     (* We have [ts1=ts2=[]] since [t1] and [t2] are in whnf. *)
     let p = add_constr c a b p in
     let x,u,v,c' = unbind_tbinder2 c a f g in
     add_constr c' u v p

  | Symb(s1), Symb(s2) when s1.sym_rules = [] && s2.sym_rules = [] ->
     if s1 == s2 && n1 = n2 then add_constr_args c ts1 ts2 p
     else fatal "[%a] and [%a] are not convertible\n" pp h1 pp h2

  | Symb(s1), Symb(s2) when s1==s2 && n1 = 0 && n2 = 0 -> p

  | Meta(m1,a1), Meta(m2,a2)
    when m1==m2 && Array.for_all2 equal_vari a1 a2 && n1 = 0 && n2 = 0 -> p

  | Meta(m,a), _ when n1 = 0 && distinct_vars a && not (occurs m t2) ->
     let b = Array.map to_var a in
     Unif.set_meta m (Bindlib.unbox (Bindlib.bind_mvar b (lift t2)));
     recompute_constrs p

  | _, Meta(m,a) when n2 = 0 && distinct_vars a && not (occurs m t1) ->
     let b = Array.map to_var a in
     Unif.set_meta m (Bindlib.unbox (Bindlib.bind_mvar b (lift t1)));
     recompute_constrs p

  | Meta(_,_), _
  | _, Meta(_,_) -> raw_add_constr c t1 t2 p

  | Symb(_), _
  | _, Symb(_) -> if eq_modulo t1 t2 then p else raw_add_constr c t1 t2 p
  (*FIXME? detect whether [t1] or [t2] can be reduced after instantiation*)

  | _, _ -> fatal "[%a] and [%a] are not convertible\n" pp h1 pp h2

and raw_add_constr c t1 t2 p =
  if !debug_unif then log "CSTR" (gre "%a ~ %a") pp t1 pp t2;
  (c,t1,t2)::p

(** [recompute_constrs p] iterates [add_constr] on [p]. *)
and recompute_constrs (p:problem) : problem =
  let fn p (c,a,b) = add_constr c a b p in
  List.fold_left fn [] p

(** [add_constr_args c ts1 ts2 p] extends [p] with possibly new
    constraints for the terms of [ts1] and [ts2] to be pairwise
    convertible in context [c]. [ts1] and [ts2] must have the same
    length. *)
and add_constr_args (c:ctxt) (ts1:term list) (ts2:term list) (p:problem)
    : problem =
  let fn p a b = add_constr c a b p in
  List.fold_left2 fn p ts1 ts2

(** Solve constraints. *)
let solve (p:problem) : unit =
  match p with
  | (_,a,b)::_ -> fatal "cannot solve the constraint [%a] ~ [%a]\n" pp a pp b
  | [] -> ()

(** [has_type c t u] returns [true] iff [t] has type [u] in context
    [c]. *)
let has_type (c:ctxt) (t:term) (u:term) : bool =
  let p = check [] c t u in
  solve p;
  true

(** [sort_type c t] returns [true] iff [t] has type a sort in context
    [c]. *)
let sort_type (c:ctxt) (t:term) : term =
  let p, typ_t = infer [] c t in
  solve p;
  let typ_t = whnf typ_t in
  match typ_t with
  | Type | Kind -> typ_t
  | _ -> fatal "[%a] has type [%a] (not a sort)...\n" pp t pp typ_t

(** If [infer c t] returns [Some u], then [t] has type [u] in context
    [c]. If it returns [None] then some constraints could not be
    solved. *)
let infer (c:ctxt) (t:term) : term option =
  let p, typ_t = infer [] c t in
  solve p;
  Some typ_t
