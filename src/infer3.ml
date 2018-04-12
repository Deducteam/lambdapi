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

let make_prod_with_domain t c no =
  let vs = List.map fst c in
  let bvs = Array.of_list (List.map _Vari vs) in
  let m' = new_meta Kind 0 (*FIXME*) in
  let typ_m = Bindlib.unbox (_Meta m' bvs) in
  let m = new_meta typ_m (Array.length bvs + 1) in
  let f x = _Meta m (Array.append bvs [|_Vari x|]) in
  let n = match no with Some n -> n | None -> "x" in
  Bindlib.unbox (_Prod t n f)

let make_prod c no =
  let vs = Array.of_list (List.map fst c) in
  let bvs = Array.map _Vari vs in
  (* Metavariable for the domain. *)
  let m1 = new_meta Kind 0 (*FIXME?*) in
  let typ_md = prod_ctxt c (Meta(m1,[||])) in
  let md = new_meta typ_md (Array.length vs) in
  let d = Meta md vs in
  (* Metavariable for the codomain. *)
  let n = match no with Some n -> n | None -> "x" in
  let x = Bindlib.new_var _Vari n in
  let m2 = new_meta Kind 0 (*FIXME?*) in
  let typ_mc = prod_ctxt ((x,d)::c) (Meta(m2,[||])) in
  let mc = new_meta typ_mc (Array.length vs + 1) in
  let f x = _Meta mc (Array.append bvs [|_Vari x|]) in
  Bindlib.unbox (_Prod d n f)

(** Constraints. *)

type typing = ctxt * term * term

type problem = typing list * term list * unif list * unif list

type strat =
  | Typ | Sort | Unif | Whnf_Unif | CheckEnd
  | Repeat of strat list

let example = Repeat [Sort; Typ; Unif; Whnf_Unif; CheckEnd]

let rec solve strats ((typs, sorts, unifs, whnf_unifs) as p) : unit =
  match strats with
  | [] -> ()
  | strat :: strats ->
     match s with
     | Typ -> solve_typs strats p
     | Sort -> solve_sorts strats p
     | Unif -> solve_unifs starts p
     | Whnf_Unif -> solve_whnf_unifs starts p
     | Repeat l' -> solve (l' @ strats) p
     | CheckEnd ->
        if typs = [] && sorts = [] && unifs = [] then
          if whnf_unifs <> [] then fatal "cannot solve constraints\n"
          else ()

and solve_typs strat ((typs, sorts, unifs, whnf_unifs) as p) : unit =
  match typs with
  | [] -> ()
  | (c,t,a)::l -> solve_typ c t a strat (l,sorts,unifs,whnf_unifs)

and solve_sorts strat ((typs, sorts, unifs, whnf_unifs) as p) : unit =
  match sorts with
  | [] -> ()
  | a::l ->
     match unfold a with
     | Type | Kind -> solve_sorts strat (typs,l,unifs,whnf_unifs)
     | _ -> fatal "[%a] not a sort\n"

and solve_unifs strat ((typs, sorts, unifs, whnf_unifs) as p) : unit =
  match unifs with
  | [] -> ()
  | (c,t,u)::l -> solve_unif c t u strat (typs,sorts,l,whnf_unifs)

and solve_whnf_unifs strat ((typs, sorts, unifs, whnf_unifs) as p) : unit =
  match whnf_unifs with
  | [] -> ()
  | (c,t,u)::l -> solve_whnf_unif c t u strat (typs,sorts,unifs,l)

and solve_typ c t a strat ((typs, sorts, unifs, whnf_unifs) as p) =
  if !debug_type then log "typing" "[%a] [%a]" pp t pp a;
  match unfold t with
  | Patt(_,_,_) | TEnv(_,_) | Kind -> assert false

  | Type -> solve (Unif::Typ::strat) (typs,sorts,(c,a,Kind)::unifs,whnf_unifs)

  | Vari(x) ->
     let typ_x = try find_tvar x c with Not_found -> assert false in
     solve (Unif::Typ::strat) (typs,sorts,(c,a,typ_x)::unifs,whnf_unifs)

  | Symb(s) ->
     solve (Unif::Typ::strat) (typs,sorts,(c,a,s.sym_type)::unifs,whnf_unifs)

  | Prod(t,f) ->
     let _,u,c' = unbind_tbinder c t f in
     solve (Typ::Sort::strat)
       ((c,t,Type)::(c',u,a)::typs,a::sorts,unifs,whnf_unifs)

  | Abst(t,b_binder) ->
     let p = make_prod t c (Some(Bindlib.binder_name b_binder)) in
     begin
       match p with
       | Prod(_,u_binder) ->
          let _,b,u,c' = unbind_tbinder2 c t b_binder u_binder in
          solve (Unif::Typ::strat)
            ((c,t,Type)::(c',b,u)::typs,sorts,(c,a,p)::unifs,whnf_unifs)
       | _ -> assert false
     end

  | Appl(t,u) ->
     let p = make_prod t c (Some(Bindlib.binder_name b_binder)) in
     solve (strat)
       (typs,sorts,unifs,whnf_unifs)
     begin
       let typ_t = raw_infer c t in
       let typ_t = whnf typ_t in
       begin
         match typ_t with
         | Meta(m,ts) when can_instantiate m && distinct_vars ts ->
            to_prod m ts None
         | _ -> ()
       end;
       match unfold typ_t with
       | Prod(b,g) -> raw_check c u b; add_constraint c a (Bindlib.subst g u)
       | _ -> fatal "[%a] is not a product\n" pp typ_t
     end

  | Meta(m, ts) ->
     (* The type of [Meta(m,ts)] is the same as [add_args v ts]
        where [v] is some fresh variable with the same type as [m]. *)
     begin
       let v = Bindlib.new_var mkfree (meta_name m) in
       let c' = add_tvar v m.meta_type c in
       raw_check c' (add_args (Vari v) (Array.to_list ts)) a
     end

let constraints : problem list ref = ref []

let generate_constraints : bool ref = ref true

let raw_add_constraint c t1 t2 =
  if !generate_constraints then
    begin
      if !debug_unif then log "raw_add_constraint" "[%a] [%a]" pp t1 pp t2;
      constraints := (c,t1,t2)::!constraints
    end
  else
    begin
      err "[%a] is not convertible to [%a]\n" pp t1 pp t2;
      raise Exit
    end

let without_generating_constraints : ('a -> 'b) -> 'a -> 'b = fun fn x ->
  try
    generate_constraints := false;
    let res = fn x in
    generate_constraints := true;
    res
  with e -> generate_constraints := true; raise e

let constraints_of : ('a -> 'b) -> 'a -> problem list * 'b = fun fn e ->
  try
    constraints := [];
    let r = fn e in
    let cs = !constraints in
    constraints := [];
    (cs, r)
  with e -> constraints := []; raise e

let can_instantiate (m:meta) : bool = !generate_constraints || internal m

(** [add_constraint c t1 t2] extends [!constraints] with possibly new
    constraints for [t1] to be convertible to [t2] in context [c]. We
    assume that, for every [i], either [ti] is [Kind] or [ti] is
    typable. *)
let rec add_constraint (c:ctxt) (t1:term) (t2:term) : unit =
  add_constraints [c,t1,t2]

and add_constraints (l:problem list) : unit =
  match l with
  | [] -> ()
  | (c,t1,t2)::l ->
     if t1 == t2 then add_constraints l
     else
       begin
         if !debug_unif then log "unif" "[%a] [%a]" pp t1 pp t2;
         match unfold t1, unfold t2 with
         | Type, Type
         | Kind, Kind -> add_constraints l

         | Vari x, Vari y when Bindlib.eq_vars x y -> add_constraints l

         | Prod(a,f), Prod(b,g)
         | Abst(a,f), Abst(b,g) ->
            let _,u,v,c' = unbind_tbinder2 c a f g in
            add_constraints ((c,a,b)::(c',u,v)::l)

         | Symb(s1), Symb(s2) when s1 == s2 -> add_constraints l

         | Meta(m1,a1), Meta(m2,a2)
           when m1==m2 && Array.for_all2 equal_vari a1 a2 ->
            add_constraints l

         | Meta(m,ts), _
           when can_instantiate m && distinct_vars ts && not (occurs m t2) ->
            instantiate m ts t2 add_constraints l

         | _, Meta(m,ts)
           when can_instantiate m && distinct_vars ts && not (occurs m t1) ->
            instantiate m ts t1 add_constraints l

         | Meta(_,_), _
         | _, Meta(_,_) -> raw_add_constraint c t1 t2; add_constraints l

         | Symb(_), _
         | _, Symb(_)
         | Appl(_,_), _
         | _, Appl(_,_) ->
            begin
              if not (Terms.eq t1 t2) then add_constraint_whnf c t1 t2;
              add_constraints l
            end

         | _, _ ->
            fatal "[%a] and [%a] are not convertible\n" pp t1 pp t2
       end

(** [add_constraint_whnf c t1 t2] normalizes [t1] and [t2] and extends
    [!constraints] with possibly new constraints for [t1] to be
    convertible to [t2] in context [c]. We assume that, for every [i],
    either [ti] is [Kind] or [ti] is typable. We also assume that [t1]
    and [t2] are in whnf. *)
and add_constraint_whnf (c:ctxt) (t1:term) (t2:term) : unit =
  add_constraints_whnf [c,t1,t2]

and add_constraints_whnf (l:problem list) : unit =
  match l with
  | [] -> ()
  | (c,t1,t2)::l ->
     let t1 = whnf t1 and t2 = whnf t2 in
     if !debug_unif then log "unif" "[%a] [%a]" pp t1 pp t2;
     let h1, ts1 = get_args t1 and h2, ts2 = get_args t2 in
     let n1 = List.length ts1 and n2 = List.length ts2 in
     match h1, h2 with
     | Type, Type
     | Kind, Kind -> add_constraints_whnf l
     (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)

     | Vari x, Vari y when Bindlib.eq_vars x y && n1 = n2 ->
        add_constraints_whnf_args c ts1 ts2 l

     | Prod(a,f), Prod(b,g)
     (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)
     | Abst(a,f), Abst(b,g) ->
     (* We have [ts1=ts2=[]] since [t1] and [t2] are in whnf. *)
        let _,u,v,c' = unbind_tbinder2 c a f g in
        add_constraints_whnf ((c,a,b)::(c',u,v)::l)

     | Symb(s1), Symb(s2) when s1.sym_rules = [] && s2.sym_rules = [] ->
        if s1 == s2 && n1 = n2 then add_constraints_whnf_args c ts1 ts2 l
        else fatal "[%a] and [%a] are not convertible\n" pp t1 pp t2

     | Symb(s1), Symb(s2) when s1==s2 && n1 = 0 && n2 = 0 ->
        add_constraints_whnf l

     | Meta(m1,a1), Meta(m2,a2)
       when m1==m2 && Array.for_all2 equal_vari a1 a2 && n1 = 0 && n2 = 0 ->
        add_constraints_whnf l

     | Meta(m,ts), _ when can_instantiate m
         && n1 = 0 && distinct_vars ts && not (occurs m t2) ->
        instantiate m ts t2 add_constraints_whnf l

     | _, Meta(m,ts) when can_instantiate m
         && n2 = 0 && distinct_vars ts && not (occurs m t1) ->
        instantiate m ts t1 add_constraints_whnf l

     | Meta(_,_), _
     | _, Meta(_,_) -> raw_add_constraint c t1 t2; add_constraints_whnf l

     | Symb(_), _
     | _, Symb(_) ->
        begin
          if not (eq_modulo t1 t2) then raw_add_constraint c t1 t2;
          add_constraints_whnf l
        end
     (*FIXME? try to detect whether [t1] or [t2] can be reduced after
       instantiation*)

     | _, _ -> fatal "[%a] and [%a] are not convertible\n" pp t1 pp t2

(** Instantiate [m[t1,..,tn]] by [v], and recompute [!constraints]. We
    assume that [t1,..,tn] are distinct variables and that [m] does
    not occur in [v]. Fails if [v] contains free variables distinct
    from [t1,..,tn]. *)
and instantiate (m:meta) (ts:term array) (v:term)
    (add_constr : problem list -> unit) (l:problem list) : unit =
  let xs = Array.map to_var ts in
  let bv = Bindlib.bind_mvar xs (lift v) in
  if Bindlib.is_closed bv then
    begin
      Unif.set_meta m (Bindlib.unbox bv);
      let cs = !constraints in
      constraints := [];
      add_constr (l @ cs)
    end
  else fatal "cannot instantiate %a[%a] by [%a]"
    pp_meta m (Array.pp pp ",") ts pp v

(** [add_constraint_args c ts1 ts2 p] extends [p] with possibly new
    constraints for the terms of [ts1] and [ts2] to be pairwise
    convertible in context [c]. [ts1] and [ts2] must have the same
    length. *)
and add_constraints_whnf_args
    (c:ctxt) (ts1:term list) (ts2:term list) (l:problem list) : unit =
  add_constraints_whnf
    (List.fold_left2 (fun l t1 t2 -> (c,t1,t2)::l) l ts1 ts2)

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
  instantiate m ts p add_constraints []

(** [raw_infer c t] returns a type for [t] in [c]. *)
let rec raw_infer (c:ctxt) (t:term) : term =
  if !debug_type then log "infer" "[%a]" pp t;
  let m_vs = create_meta c in
  raw_check c t m_vs;
  m_vs

(** [raw_check c t a] checks that [t] is of type [a] in [c]. [a] must be
    [Kind] or be typable by a sort. *)
and raw_check (c:ctxt) (t:term) (a:term) : unit =
  if !debug_type then log "typing" "[%a] [%a]" pp t pp a;
  match unfold t with
  | Patt(_,_,_) | TEnv(_,_) | Kind -> assert false

  | Type -> add_constraint c a Kind

  | Vari(x) ->
     let typ_x = try find_tvar x c with Not_found -> assert false in
     add_constraint c a typ_x

  | Symb(s) -> add_constraint c a s.sym_type

  | Prod(t,f) ->
     begin
       raw_check c t Type;
       let _,u,c' = unbind_tbinder c t f in
       raw_check c' u a;
       match unfold a with
       | Type | Kind -> ()
       | _ -> fatal "[%a] is not a sort\n" pp a
     end

  | Abst(t,f) ->
     begin
       raw_check c t Type;
       let a = whnf a in
       begin
         match a with
         | Meta(m,ts) when can_instantiate m && distinct_vars ts ->
            to_prod m ts (Some(Bindlib.binder_name f))
         | _ -> ()
       end;
       match unfold a with
       | Prod(b,g) ->
          begin
            add_constraint c b t;
            let _,u,d,c' = unbind_tbinder2 c t f g in
            raw_check c' u d
          end
       | _ -> fatal "[%a] is not a product\n" pp a
     end

  | Appl(t,u) ->
     begin
       let typ_t = raw_infer c t in
       let typ_t = whnf typ_t in
       begin
         match typ_t with
         | Meta(m,ts) when can_instantiate m && distinct_vars ts ->
            to_prod m ts None
         | _ -> ()
       end;
       match unfold typ_t with
       | Prod(b,g) -> raw_check c u b; add_constraint c a (Bindlib.subst g u)
       | _ -> fatal "[%a] is not a product\n" pp typ_t
     end

  | Meta(m, ts) ->
     (* The type of [Meta(m,ts)] is the same as [add_args v ts]
        where [v] is some fresh variable with the same type as [m]. *)
     begin
       let v = Bindlib.new_var mkfree (meta_name m) in
       let c' = add_tvar v m.meta_type c in
       raw_check c' (add_args (Vari v) (Array.to_list ts)) a
     end

(** Solve constraints. *)
let solve : problem list -> bool = fun cs ->
  let msg (_,a,b) = wrn "Cannot solve constraint [%a] ~ [%a]\n" pp a pp b in
  List.iter msg cs; cs = []

(** [has_type c t u] returns [true] iff [t] has type [u] in context [c]. *)
let has_type : ctxt -> term -> term -> bool = fun ctxt t a ->
  let (cs, _) = constraints_of (raw_check ctxt t) a in
  solve cs

(** [sort_type c t] returns [true] iff [t] has type a sort in context [c]. *)
let sort_type : ctxt -> term -> term = fun ctx a ->
  let (cs, s) = constraints_of (raw_infer ctx) a in
  if not (solve cs) then fatal "Constraints cannot be solved.\n";
  match unfold s with
  | Type
  | Kind -> s
  | _    -> fatal "[%a] has type [%a] (not a sort)...\n" pp a pp s

(** If [infer c t] returns [Some u], then [t] has type [u] in context
    [c]. If it returns [None] then some constraints could not be solved. *)
let infer : ctxt -> term -> term option = fun ctx t ->
  let (cs, a) = constraints_of (raw_infer ctx) t in
  if not (solve cs) then None else Some(a)
