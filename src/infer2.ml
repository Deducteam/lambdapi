(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console
open Eval

(** [equal_vari t u] checks that [t] and [u] are the same variable. *)
let equal_vari (t:term) (u:term) : bool =
  match t, u with
  | Vari x, Vari y -> Bindlib.eq_vars x y
  | _, _ -> false

(** Unification problem. *)
type unif = Ctxt.t * term * term

let pp_unif : unif pp = fun oc (_,t,u) ->
  Printf.fprintf oc "%a = %a" pp t pp u

let pp_unifs : unif list pp = fun oc l ->
  match l with
  | [] -> ()
  | _ -> Printf.fprintf oc " if %a" (List.pp pp_unif ", ") l

(** Constraints. *)

let constraints : unif list ref = ref []

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

let constraints_of : ('a -> 'b) -> 'a -> unif list * 'b = fun fn e ->
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
let rec add_constraint (c:Ctxt.t) (t1:term) (t2:term) : unit =
  add_constraints [c,t1,t2]

and add_constraints (l:unif list) : unit =
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
            let (c',u,v) = Ctxt.unbind2 c a f g in
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
and add_constraint_whnf (c:Ctxt.t) (t1:term) (t2:term) : unit =
  add_constraints_whnf [c,t1,t2]

and add_constraints_whnf (l:unif list) : unit =
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
        let (c',u,v) = Ctxt.unbind2 c a f g in
        add_constraints_whnf ((c,a,b)::(c',u,v)::l)

     | Symb(s1), Symb(s2) when !(s1.sym_rules) = [] && !(s2.sym_rules) = [] ->
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
    (add_constr : unif list -> unit) (l:unif list) : unit =
  let xs = to_tvars ts in
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
    (c:Ctxt.t) (ts1:term list) (ts2:term list) (l:unif list) : unit =
  add_constraints_whnf
    (List.fold_left2 (fun l t1 t2 -> (c,t1,t2)::l) l ts1 ts2)

(** [create_meta c] creates a term [m[x1,,,xn]] where [m] is a new
    metavariable and [x1,..,xn] are the variables of [c]. *)
let create_meta (c:Ctxt.t) : term =
  let typ_m = Ctxt.to_prod c Type in
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
let rec raw_infer (c:Ctxt.t) (t:term) : term =
  if !debug_type then log "infer" "[%a]" pp t;
  let m_vs = create_meta c in
  raw_check c t m_vs;
  m_vs

(** [raw_check c t a] checks that [t] is of type [a] in [c]. [a] must be
    [Kind] or be typable by a sort. *)
and raw_check (c:Ctxt.t) (t:term) (a:term) : unit =
  if !debug_type then log "typing" "[%a] [%a]" pp t pp a;
  match unfold t with
  | Patt(_,_,_) | TEnv(_,_) | Kind -> assert false

  | Type -> add_constraint c a Kind

  | Vari(x) ->
     let typ_x = try Ctxt.find x c with Not_found -> assert false in
     add_constraint c a typ_x

  | Symb(s) -> add_constraint c a !(s.sym_type)

  | Prod(t,f) ->
     begin
       raw_check c t Type;
       let (c',u) = Ctxt.unbind c t f in
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
            let (c',u,d) = Ctxt.unbind2 c t f g in
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
       let c' = Ctxt.add v m.meta_type c in
       raw_check c' (add_args (Vari v) (Array.to_list ts)) a
     end

(** Solve constraints. *)
let solve : unif list -> bool = fun cs ->
  let msg (_,a,b) = wrn "Cannot solve constraint [%a] ~ [%a]\n" pp a pp b in
  List.iter msg cs; cs = []

(** [has_type c t u] returns [true] iff [t] has type [u] in context [c]. *)
let has_type : Ctxt.t -> term -> term -> bool = fun ctxt t a ->
  let (cs, _) = constraints_of (raw_check ctxt t) a in
  solve cs

(** [sort_type c t] returns [true] iff [t] has type a sort in context [c]. *)
let sort_type : Ctxt.t -> term -> term = fun ctx a ->
  let (cs, s) = constraints_of (raw_infer ctx) a in
  if not (solve cs) then fatal "Constraints cannot be solved.\n";
  match unfold s with
  | Type
  | Kind -> s
  | _    -> fatal "[%a] has type [%a] (not a sort)...\n" pp a pp s

(** If [infer c t] returns [Some u], then [t] has type [u] in context
    [c]. If it returns [None] then some constraints could not be solved. *)
let infer : Ctxt.t -> term -> term option = fun ctx t ->
  let (cs, a) = constraints_of (raw_infer ctx) t in
  if not (solve cs) then None else Some(a)
