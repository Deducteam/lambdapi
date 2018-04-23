(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console
open Eval

type ctxt = Ctxt.t

(** [equal_vari t u] checks that [t] and [u] are the same variable. *)
let equal_vari (t:term) (u:term) : bool =
  match t, u with
  | Vari x, Vari y -> Bindlib.eq_vars x y
  | _, _ -> false

(** [make_meta c] creates a term [m[x1,..,xn]] of type [t] where [m]
    is a new metavariable and [x1,..,xn] are the variables of [c]. *)
let make_meta (c:ctxt) (t:term) : term =
  let typ_m = Ctxt.to_prod c t in
  let m = new_meta typ_m (List.length c) in
  let vs = List.rev_map (fun (v,_) -> Vari v) c in
  Meta(m, Array.of_list vs)

(** [make_meta_sort] creates a term [m[]] where [m] is a metavariable
    that should be instantiated by a sort. *)
let make_sort() : term = (*make_meta [] Kind*)
  Meta(new_meta Kind 0,[||])

(** [make_codomain c no t] creates a term [m[x1,..,xn,x]] of type a
    sort where [x1,..,xn] are the variables of [c] and [x] a new variable
    of name [no]. *)
let make_codomain c no t =
  let n = match no with Some n -> n | None -> "x" in
  let x = Bindlib.new_var mkfree n in
  let u = make_meta ((x,t)::c) (make_sort()) in
  Bindlib.unbox (Bindlib.bind_var x (lift u))

(** [make_prod c no] creates a term [x:m1[x1,..,xn]->m2[x1,..,xn,x]]
    of type a sort where [x1,..,xn] are the variables of [c] and [x] a
    new variable of name [no]. *)
let make_prod c no =
  let d = make_meta c (make_sort()) in
  d, make_codomain c no d

type typing = ctxt * term * term

type unif = ctxt * term * term

let pp_unif : unif pp = fun oc (_,t,u) ->
  Printf.fprintf oc "%a = %a" pp t pp u

let pp_unifs : unif list pp = fun oc l ->
  match l with
  | [] -> ()
  | _ -> Printf.fprintf oc " if %a" (List.pp pp_unif ", ") l

type problem = typing list * term list * unif list * unif list * unif list

type strat =
  | Typ | Sort | Unif | Whnf | CheckEnd
  | Repeat of strat list

let rec pp_strat : strat pp = fun oc strat ->
  match strat with
  | Typ -> output_string oc "T"
  | Sort -> output_string oc "S"
  | Unif -> output_string oc "U"
  | Whnf -> output_string oc "W"
  | CheckEnd -> output_string oc "E"
  | Repeat strats -> Printf.fprintf oc "[%a]" pp_strats strats

and pp_strats : strat list pp = fun oc strats -> List.pp pp_strat "" oc strats

let default_strat = Repeat [Typ; Sort; Unif; Whnf; CheckEnd]

let can_instantiate : bool ref = ref true

let recompute : bool ref = ref false

let instantiate (m:meta) (ts:term array) (v:term) : bool =
  (!can_instantiate || internal m) && distinct_vars ts && not (occurs m v) &&
  let bv = Bindlib.bind_mvar (to_tvars ts) (lift v) in
  Bindlib.is_closed bv &&
    (Unif.set_meta m (Bindlib.unbox bv); recompute := true; true)

exception Exit_solve

let not_convertible t1 t2 =
  err "[%a] and [%a] are not convertible\n" pp t1 pp t2;
  raise Exit_solve

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

and solve_typs strats ((typs,sorts,unifs,whnfs,unsolved) as p) : unif list =
  match typs with
  | [] -> solve strats p
  | (c,t,a)::l -> solve_typ c t a strats (l,sorts,unifs,whnfs,unsolved)

and solve_sorts strats ((typs,sorts,unifs,whnfs,unsolved) as p) : unif list =
  match sorts with
  | [] -> solve strats p
  | a::l -> solve_sort a strats (typs,l,unifs,whnfs,unsolved)

and solve_unifs strats ((typs,sorts,unifs,whnfs,unsolved) as p) : unif list =
  match unifs with
  | [] -> solve strats p
  | (c,t,u)::l -> solve_unif c t u strats (typs,sorts,l,whnfs,unsolved)

and solve_whnfs strats ((typs,sorts,unifs,whnfs,unsolved) as p)
    : unif list =
  match whnfs with
  | [] -> solve strats p
  | (c,t,u)::l -> solve_whnf c t u strats (typs,sorts,unifs,l,unsolved)

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
     let u_binder = make_codomain c no t in
     let p = Prod(t,u_binder) in
     let c',b,u = Ctxt.unbind2 c t b_binder u_binder in
     solve (Typ::Unif::strats)
       ((c,t,Type)::(c',b,u)::typs,sorts,(c,p,a)::unifs,whnfs,unsolved)

  | Appl(t,u) ->
     let v, w_binder = make_prod c None in
     let p = Prod(v, w_binder) in
     let a' = Bindlib.subst w_binder u in
     solve (Typ::Unif::strats)
       ((c,t,p)::(c,u,v)::typs,sorts,(c,a',a)::unifs,whnfs,unsolved)

  | Meta(m, ts) ->
     (* The type of [Meta(m,ts)] is the same as [add_args v ts]
        where [v] is some fresh variable with the same type as [m]. *)
     let v = Bindlib.new_var mkfree (meta_name m) in
     let c' = Ctxt.add v m.meta_type c in
     let t' = add_args (Vari v) (Array.to_list ts) in
     solve_typ c' t' a strats p

and solve_sort a strats p : unif list =
  if !debug_type then log "solve_sort" "[%a]" pp a;
  match unfold a with
  | Type | Kind -> solve_sorts strats p
  | _ -> fatal "[%a] is not a sort\n" pp a

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

      | Symb(s), _ when !(s.sym_rules) <> [] ->
         solve (Unif::strats) (typs,sorts,unifs,(c,t1,t2)::whnfs,unsolved)

      | _, Symb(s) when !(s.sym_rules) <> [] ->
         solve (Unif::strats) (typs,sorts,unifs,(c,t1,t2)::whnfs,unsolved)

      | Appl(_,_), _ | _, Appl(_,_) ->
         solve (Unif::strats) (typs,sorts,unifs,(c,t1,t2)::whnfs,unsolved)

      | _, _ -> not_convertible t1 t2
    end

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

  | Symb(s1), Symb(s2) when !(s1.sym_rules) = [] && !(s2.sym_rules) = [] ->
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

  | Symb(s), _ when !(s.sym_rules) <> [] ->
     if eq_modulo t1 t2 then solve (Whnf::strats) p
     else solve (Whnf::strats) (typs,sorts,unifs,whnfs,(c,t1,t2)::unsolved)

  | _, Symb(s) when !(s.sym_rules) <> [] ->
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
  if !debug_type then log "has_type" "[%a] [%a]" pp t pp a;
  match solve true [default_strat] ([c,t,a],[],[],[],[]) with
  | Some l -> List.iter msg l; l = []
  | None -> false

(** [has_type_no_inst c t u] returns [true] iff [t] has type [u] in
    context [c] without instantiating any metavariable. *)
let has_type_no_inst (c:ctxt) (t:term) (a:term) : bool =
  if !debug_type then log "has_type_no_inst" "[%a] [%a]" pp t pp a;
  match solve false [default_strat] ([c,t,a],[],[],[],[]) with
  | Some l -> List.iter msg l; l = []
  | None -> false

(** [constrained_infer c t] returns a pair [a,l] where [l] is a list
    of unification problems for [a] to be the type of [t] in context [c]. *)
let constrained_infer (c:ctxt) (t:term) : unif list * term =
  if !debug_type then log "constrained_infer" "[%a]" pp t;
  let a = make_meta c (make_sort()) in
  match solve true [default_strat] ([c,t,a],[],[],[],[]) with
  | Some l -> l, a
  | None -> raise Fatal

(** [infer c t] returns [Some u] if [t] has type [u] in context [c],
    and [None] otherwise. *)
let infer (c:ctxt) (t:term) : term option =
  let l, a = constrained_infer c t in
  if l = [] then Some a else (List.iter msg l; None)

(** [sort_type c t] returns [true] iff [t] has type a sort in context [c]. *)
let sort_type (c:ctxt) (t:term) : term =
  if !debug_type then log "sort_type" "[%a]" pp t;
  let a = make_meta c (make_sort()) in
  match solve true [default_strat] ([c,t,a],[],[],[],[]) with
  | Some [] ->
     begin
       match unfold a with
       | Type | Kind -> a
       | _    -> fatal "[%a] has type [%a] (not a sort)...\n" pp t pp a
     end
  | Some l -> List.iter msg l; raise Fatal
  | None -> raise Fatal
