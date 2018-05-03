(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console
open Eval

type ctxt = Ctxt.t

(** [equal_vari t u] checks that [t] and [u] are variables and are equal. *)
let equal_vari : term -> term -> bool = fun t u ->
  match (unfold t, unfold u) with
  | (Vari x, Vari y) -> Bindlib.eq_vars x y
  | (_     , _     ) -> false

(** [make_type ()] generates a term [m[]] where [m] is a fresh metavariable of
    arity [0] and type [Type]. *)
let make_type () = Meta(new_meta Type 0, [||])

(** [make_meta c t] creates a term [m[x1,..,xn]] of type [t] where [m] is a
    new metavariable and [x1,..,xn] are the variables of [c]. *)
let make_meta : ctxt -> term -> term = fun c t ->
  let typ_m = Ctxt.to_prod c t in
  let m = new_meta typ_m (List.length c) in
  let vs = List.rev_map (fun (v,_) -> Vari v) c in
  Meta(m, Array.of_list vs)

(** [make_binder c no d] creates a binder obtained by binding v in the
    term [m[x1,..,xn,v]] of type a sort where [x1,..,xn] are the
    variables of [c] and [v] is a new variable of name [no]. *)
let make_binder (c:ctxt) (no:string option) (d:term) : tbinder =
  let n = match no with Some n -> n | None -> "x" in
  let v = Bindlib.new_var mkfree n in
  let u = make_meta ((v,d)::c) (make_type()) in
  Bindlib.unbox (Bindlib.bind_var v (lift u))

(** [make_prod c] creates a term [x:m1[x1,..,xn]->m2[x1,..,xn,x]] of
    type a sort where [x1,..,xn] are the variables of [c] and [x] is a
    new variable of name [no]. *)
let make_prod c =
  let d = make_meta c (make_type()) in d, make_binder c None d

(** Representation of typing problems. *)
type typing = ctxt * term * term

(** Representation of unification problems. *)
type unif = ctxt * term * term

let pp_unif : unif pp = fun oc (_,t,u) ->
  Printf.fprintf oc "%a = %a" pp t pp u

let pp_unifs : unif list pp = fun oc l ->
  match l with
  | [] -> ()
  | _ -> Printf.fprintf oc " if %a" (List.pp pp_unif ", ") l

(** Representation of problems:
    1. a list of typing problems;
    2. a list of sort problems, that is, terms whose types must be sorts;
    3. a list of unification problems;
    4. a list of unification problems that must weak-head-normalized first;
    5. a list of unification problems that have not been solved yet. *)

type problem = typing list * term list * unif list * unif list * unif list

(** Representation of solving strategies. *)
type strat =
  | Typ (** deal with typing problems *)
  | Sort (** deal with sorting problems *)
  | Unif (** deal with unification problems *)
  | Whnf
  (** deal with unification problems that must be weak-head-normalized first *)
  | CheckEnd (** check whether there is something else we can do *)
  | Repeat of strat list (** repeat a list of strategies *)

let rec pp_strat : strat pp = fun oc strat ->
  match strat with
  | Typ -> output_string oc "T"
  | Sort -> output_string oc "S"
  | Unif -> output_string oc "U"
  | Whnf -> output_string oc "W"
  | CheckEnd -> output_string oc "E"
  | Repeat strats -> Printf.fprintf oc "[%a]" pp_strats strats

and pp_strats : strat list pp = fun oc strats -> List.pp pp_strat "" oc strats

(** Default strategy. *)
let default_strat = Repeat [Typ; Sort; Unif; Whnf; CheckEnd]

(** [set_meta m v] sets the value of the metavariable [m] to [v]. *)
let set_meta : meta -> (term, term) Bindlib.mbinder -> unit = fun m v ->
  if !debug_unif then
    begin
      let (xs,v) = Bindlib.unmbind mkfree v in
      log "set_meta" "%a[%a] ← %a" pp_meta m (Array.pp pp_tvar ",") xs pp v
    end;
  begin
    match m.meta_name with
    | Defined(s)  -> let str_map = StrMap.remove s !all_metas.str_map in
                     all_metas := {!all_metas with str_map}
    | Internal(i) -> let int_map = IntMap.remove i !all_metas.int_map in
                     all_metas := {!all_metas with int_map}
  end;
  m.meta_value := Some(v)

(** Boolean saying whether user metavariables can be set or not. *)
let can_instantiate : bool ref = ref true

(** Boolean saying whether unsolved unification problems need to be
    rechecked. *)
let recompute : bool ref = ref false

(** [instantiate m ts v] check whether [m] can be instantiated to
    solve the unification problem [m[ts] = v]. Actually make the
    instantiation if it is possible. *)
let instantiate (m:meta) (ts:term array) (v:term) : bool =
  (!can_instantiate || internal m) && distinct_vars ts && not (occurs m v) &&
  let bv = Bindlib.bind_mvar (to_tvars ts) (lift v) in
  Bindlib.is_closed bv &&
    (set_meta m (Bindlib.unbox bv); recompute := true; true)

(** Exception raised by the solving algorithm when an irrecuperable
    error is found. *)
exception Exit_solve

let not_convertible t1 t2 =
  err "[%a] and [%a] are not convertible\n" pp t1 pp t2;
  raise Exit_solve

(** [solve s p] tries to solve the problem [p] following the strategy
    list [s]. When it stops, it returns the list of unsolved
    unification problems. *)
let rec solve strats ((typs,sorts,unifs,whnfs,unsolved) as p) : unif list =
  if !debug then log "solve" "%a" pp_strats strats;
  match strats with
  | [] -> assert false
  | strat :: strats' ->
     match strat with
     | Typ -> solve_typs strats' p
     | Sort -> solve_sorts strats' p
     | Unif -> solve_unifs strats' p
     | Whnf -> solve_whnfs strats' p
     | Repeat l' -> solve (l' @ strats) p
     | CheckEnd ->
        if typs = [] && sorts = [] && unifs = [] && whnfs = [] then
          if unsolved = [] then []
          else if !recompute then
            begin
              recompute := false;
              solve (Unif::strats) ([],[],unsolved,[],[])
            end
          else unsolved
        else solve strats' p

(** [solve_typs s p] tries to solve the typing problems of [p]. Then,
    it continues with the remaining problems following the strategy
    list [s]. *)
and solve_typs strats ((typs,sorts,unifs,whnfs,unsolved) as p) : unif list =
  match typs with
  | [] -> solve strats p
  | (c,t,a)::l -> solve_typ c t a strats (l,sorts,unifs,whnfs,unsolved)

(** [solve_sorts s p] tries to solve the sorting problems of [p]. Then,
    it continues with the remaining problems following the strategy
    list [s]. *)
and solve_sorts strats ((typs,sorts,unifs,whnfs,unsolved) as p) : unif list =
  match sorts with
  | [] -> solve strats p
  | a::l -> solve_sort a strats (typs,l,unifs,whnfs,unsolved)

(** [solve_unifs s p] tries to solve the unification problems of
    [p]. Then, it continues with the remaining problems following the
    strategy list [s]. *)
and solve_unifs strats ((typs,sorts,unifs,whnfs,unsolved) as p) : unif list =
  match unifs with
  | [] -> solve strats p
  | (c,t,u)::l -> solve_unif c t u strats (typs,sorts,l,whnfs,unsolved)

(** [solve_whnfs s p] tries to solve the unification problems of [p]
    that msut be weak-head-normalized first. Then, it continues with
    the remaining problems following the strategy list [s]. *)
and solve_whnfs strats ((typs,sorts,unifs,whnfs,unsolved) as p)
    : unif list =
  match whnfs with
  | [] -> solve strats p
  | (c,t,u)::l -> solve_whnf c t u strats (typs,sorts,unifs,l,unsolved)

(** [solve_typ c t a s p] tries to solve the typing problem
    [(c,t,a)]. Then, it continues with the remaining problems
    following the strategy list [s]. *)
and solve_typ c t a strats ((typs,sorts,unifs,whnfs,unsolved) as p) =
  if !debug_type then log "solve_typ" "[%a] [%a]" pp t pp a;
  match unfold t with
  | Patt(_,_,_) | TEnv(_,_) | Kind -> assert false

  | Type ->
     solve (Unif::Typ::strats)
       (typs,sorts,(c,Kind,a)::unifs,whnfs,unsolved)

  | Vari(x) ->
     let typ_x = try Ctxt.find x c with Not_found -> assert false in
     solve (Unif::Typ::strats)
       (typs,sorts,(c,typ_x,a)::unifs,whnfs,unsolved)

  | Symb(s) ->
     solve (Unif::Typ::strats)
       (typs,sorts,(c,!(s.sym_type),a)::unifs,whnfs,unsolved)

  | Prod(t,u_binder) ->
     let c',u = Ctxt.unbind c t u_binder in
     solve (Typ::Sort::strats)
       ((c,t,Type)::(c',u,a)::typs,a::sorts,unifs,whnfs,unsolved)

  | Abst(t,b_binder) ->
     let no = Some(Bindlib.binder_name b_binder) in
     let u_binder = make_binder c no t in
     let p = Prod(t,u_binder) in
     let c',b,u = Ctxt.unbind2 c t b_binder u_binder in
     solve (Typ::Unif::strats)
       ((c,t,Type)::(c',b,u)::typs,sorts,(c,p,a)::unifs,whnfs,unsolved)

  | Appl(t,u) ->
     let v, w_binder = make_prod c in
     let p = Prod(v, w_binder) in
     let a' = Bindlib.subst w_binder u in
     solve (Typ::Unif::strats)
       ((c,t,p)::(c,u,v)::typs,sorts,(c,a',a)::unifs,whnfs,unsolved)

  | Meta(m, ts) ->
     (* The type of [Meta(m,ts)] is the same as [add_args f ts]
        where [f] is some fresh symbol with the same type as [m]. *)
     let s =
       { sym_name = meta_name m ; sym_type = ref m.meta_type ; sym_path = []
       ; sym_def  = ref None ; sym_rules = ref [] ; sym_const = true }
     in
     let t = add_args (Symb s) (Array.to_list ts) in
     solve_typ c t a strats p

(** [solve_sort a s p] tries to solve the sorting problem [a]. Then,
    it continues with the remaining problems following the strategy
    list [s]. *)
and solve_sort a strats p : unif list =
  if !debug_type then log "solve_sort" "[%a]" pp a;
  match unfold a with
  | Type | Kind -> solve_sorts strats p
  | _ -> fatal "[%a] is not a sort\n" pp a

(** [solve_unif c t1 t2 s p] tries to solve the unificaton problem
    [(c,t1,t2)]. Then, it continues with the remaining problems
    following the strategy list [s]. *)
and solve_unif c t1 t2 strats ((typs,sorts,unifs,whnfs,unsolved) as p)
    : unif list =
  if t1 == t2 then solve_unifs strats p
  else
    begin
      if !debug_unif then log "solve_unif" "[%a] [%a]" pp t1 pp t2;
      match unfold t1, unfold t2 with
      | Type, Type
      | Kind, Kind -> solve (Unif::strats) p

      | Vari x, Vari y when Bindlib.eq_vars x y -> solve (Unif::strats) p

      | Prod(a,f), Prod(b,g) | Abst(a,f), Abst(b,g) ->
         let c',u,v = Ctxt.unbind2 c a f g in
         solve (Unif::strats)
           (typs,sorts,(c,a,b)::(c',u,v)::unifs,whnfs,unsolved)

      | Symb(s1), Symb(s2) when s1 == s2 -> solve (Unif::strats) p

      | Meta(m1,a1), Meta(m2,a2)
        when m1==m2 && Array.for_all2 equal_vari a1 a2 ->
         solve (Unif::strats) p

      | Meta(m,ts), v when instantiate m ts v -> solve (Unif::strats) p
      | v, Meta(m,ts) when instantiate m ts v -> solve (Unif::strats) p

      | Meta(_,_), _
      | _, Meta(_,_) ->
         solve (Unif::strats) (typs,sorts,unifs,(c,t1,t2)::whnfs,unsolved)

      | Symb(s), _ when not (Sign.is_const s) ->
         solve (Unif::strats) (typs,sorts,unifs,(c,t1,t2)::whnfs,unsolved)

      | _, Symb(s) when not (Sign.is_const s) ->
         solve (Unif::strats) (typs,sorts,unifs,(c,t1,t2)::whnfs,unsolved)

      | Appl(_,_), _ | _, Appl(_,_) ->
         solve (Unif::strats) (typs,sorts,unifs,(c,t1,t2)::whnfs,unsolved)

      | _, _ -> not_convertible t1 t2
    end

(** [solve_whnf c t1 t2 s p] tries to solve the unificaton problem
    [(c,t1,t2)] by first weak-head-normalizing it first. Then, it
    continues with the remaining problems following the strategy list
    [s]. *)
and solve_whnf c t1 t2 strats ((typs,sorts,unifs,whnfs,unsolved) as p)
    : unif list =
  let t1 = whnf t1 and t2 = whnf t2 in
  if !debug_unif then log "solve_whnf" "[%a] [%a]" pp t1 pp t2;
  let h1, ts1 = get_args t1 and h2, ts2 = get_args t2 in
  let n1 = List.length ts1 and n2 = List.length ts2 in
  match h1, h2 with
  | Type, Type
  | Kind, Kind -> solve (Whnf::strats) p
  (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)

  | Vari x, Vari y when Bindlib.eq_vars x y && n1 = n2 ->
     let unifs = List.fold_left2 (fun l t1 t2 -> (c,t1,t2)::l) unifs ts1 ts2 in
     solve (Whnf::strats) (typs,sorts,unifs,whnfs,unsolved)

  | Prod(a,f), Prod(b,g)
  (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)
  | Abst(a,f), Abst(b,g) ->
  (* We have [ts1=ts2=[]] since [t1] and [t2] are in whnf. *)
     let c',u,v = Ctxt.unbind2 c a f g in
     solve (Unif::Whnf::strats)
       (typs,sorts,(c,a,b)::(c',u,v)::unifs,whnfs,unsolved)

  | Symb(s1), Symb(s2) when s1 == s2 && n1 = 0 && n2 = 0 ->
     solve (Whnf::strats) p

  | Symb(s1), Symb(s2) when Sign.is_const s1 && Sign.is_const s2 ->
     if s1 == s2 && n1 = n2 then
       let unifs =
         List.fold_left2 (fun l t1 t2 -> (c,t1,t2)::l) unifs ts1 ts2 in
       solve (Unif::Whnf::strats) (typs,sorts,unifs,whnfs,unsolved)
     else not_convertible t1 t2

  | Meta(m1,a1), Meta(m2,a2)
    when m1 == m2 && n1 = 0 && n2 = 0 && Array.for_all2 equal_vari a1 a2 ->
     solve (Whnf::strats) p

  | Meta(m,ts), _ when n1 = 0 && instantiate m ts t2 -> solve (Whnf::strats) p
  | _, Meta(m,ts) when n2 = 0 && instantiate m ts t1 -> solve (Whnf::strats) p

  | Meta(_,_), _
  | _, Meta(_,_) ->
     solve (Whnf::strats) (typs,sorts,unifs,whnfs,(c,t1,t2)::unsolved)

  | Symb(s), _ when not (Sign.is_const s) ->
     if eq_modulo t1 t2 then solve (Whnf::strats) p
     else solve (Whnf::strats) (typs,sorts,unifs,whnfs,(c,t1,t2)::unsolved)

  | _, Symb(s) when not (Sign.is_const s) ->
     if eq_modulo t1 t2 then solve (Whnf::strats) p
     else solve (Whnf::strats) (typs,sorts,unifs,whnfs,(c,t1,t2)::unsolved)

  | _, _ -> not_convertible t1 t2

(** [solve b strats p] sets [can_instantiate] to [b] and returns
    [Some(l)] if [solve strats p] returns [l], and [None] otherwise. *)
let solve b strats p : unif list option =
  can_instantiate := b;
  recompute := false;
  try Some (solve strats p) with Exit_solve -> None

let msg (_,a,b) = err "Cannot solve constraint [%a] ~ [%a]\n" pp a pp b

(** [has_type c t u] returns [true] iff [t] has type [u] in context [c]. *)
let has_type (c:ctxt) (t:term) (a:term) : bool =
  (*
  Gc.compact ();
  Printf.eprintf "==== BEFORE HAS_TYPE ====\n";
  Gc.print_stat stderr;
  Printf.eprintf "=========================\n%!";
  let res =
  *)
  if !debug_type then log "has_type" "[%a] [%a]" pp t pp a;
  match solve true [default_strat] ([c,t,a],[],[],[],[]) with
  | Some l -> List.iter msg l; l = []
  | None   -> false
  (*
  in
  Gc.compact ();
  Printf.eprintf "==== AFTER HAS_TYPE =====\n";
  Gc.print_stat stderr;
  Printf.eprintf "=========================\n%!";
  res
  *)

(** [has_type_with_constrs cs c t u] returns [true] iff [t] has type
    [u] in context [c] and constraints [cs] without instantiating any
    user-defined metavariable. *)
let has_type_with_constr (cs:unif list) (c:ctxt) (t:term) (a:term) : bool =
  if !debug_type then log "has_type_with_constrs" "[%a] [%a]" pp t pp a;
  match solve false [default_strat] ([c,t,a],[],[],[],[]) with
  | Some l ->
     let l = List.filter (fun x -> not (List.mem x cs)) l in
     List.iter msg l; l = []
  | None -> false

(** [infer_constr c t] returns a pair [a,l] where [l] is a list
    of unification problems for [a] to be the type of [t] in context [c]. *)
let infer_constr (c:ctxt) (t:term) : unif list * term =
  if !debug_type then log "infer_constr" "[%a]" pp t;
  let a = make_meta c (make_type()) in
  match solve true [default_strat] ([c,t,a],[],[],[],[]) with
  | Some l -> l, a
  | None -> raise Fatal

(** [infer c t] returns [Some u] if [t] has type [u] in context [c],
    and [None] otherwise. *)
let infer (c:ctxt) (t:term) : term option =
  let l, a = infer_constr c t in
  if l = [] then Some a else (List.iter msg l; None)

(** [sort_type c t] returns [true] iff [t] has type a sort in context [c]. *)
let sort_type (c:ctxt) (t:term) : term =
  if !debug_type then log "sort_type" "[%a]" pp t;
  let a = make_meta c (make_type()) in
  match solve true [default_strat] ([c,t,a],[],[],[],[]) with
  | Some [] ->
     begin
       match unfold a with
       | Type | Kind -> a
       | _    -> fatal "[%a] has type [%a] (not a sort)...\n" pp t pp a
     end
  | Some l -> List.iter msg l; raise Fatal
  | None -> raise Fatal
