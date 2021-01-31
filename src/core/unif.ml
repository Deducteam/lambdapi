(** Solving unification constraints. *)

open! Lplib
open Lplib.Extra

open Timed
open Backbone
open Console
open Terms
open Basics
open Env
open Print

(** Logging function for unification. *)
let log_unif = new_logger 'u' "unif" "unification"
let log_unif = log_unif.logger

(** Exception raised when a constraint is not solvable. *)
exception Unsolvable

(** [try_unif_rules ctx s t] tries to solve unification problem [ctx ⊢ s ≡ t]
   using declared unification rules. *)
let try_unif_rules : ctxt -> term -> term -> constr list option =
  fun ctx s t ->
  if !log_enabled then log_unif "check unif_rules for %a" pp_constr (ctx,s,t);
  let exception No_match in
  let open Unif_rule in
  try
    let rhs =
      match Eval.tree_walk !(equiv.sym_tree) ctx [s;t] with
      | Some(r,[]) -> r
      | Some(_)    -> assert false (* Everything should be matched *)
      | None       ->
      match Eval.tree_walk !(equiv.sym_tree) ctx [t;s] with
      | Some(r,[]) -> r
      | Some(_)    -> assert false (* Everything should be matched *)
      | None       -> raise No_match
    in
    let subpbs = List.map (fun (t,u) -> (ctx,t,u)) (unpack rhs) in
    let pp_subpbs = List.pp pp_constr "; " in
    if !log_enabled then log_unif (gre "get [%a]") pp_subpbs subpbs;
    Some(subpbs)
  with No_match ->
    if !log_enabled then log_unif "found no unif_rule";
    None

(** [nl_distinct_vars ctx ts] checks that [ts] is made of variables  [vs] only
    and returns some copy of [vs] where variables occurring more than once are
    replaced by fresh variables.  Variables defined in  [ctx] are unfolded. It
    returns [None] otherwise. *)
let nl_distinct_vars
    : ctxt -> term array -> (tvar array * tvar StrMap.t) option =
  fun ctx ts ->
  let exception Not_a_var in
  let open Stdlib in
  let vars = ref VarSet.empty
  and nl_vars = ref VarSet.empty
  and patt_vars = ref StrMap.empty in
  let rec to_var t =
    match Ctxt.unfold ctx t with
    | Vari(v) ->
        if VarSet.mem v !vars then nl_vars := VarSet.add v !nl_vars
        else vars := VarSet.add v !vars;
        v
    | Symb(f) when f.sym_name <> "" && f.sym_name.[0] = '$' ->
        (* Symbols replacing pattern variables are considered as variables. *)
        let v =
          try StrMap.find f.sym_name !patt_vars
          with Not_found ->
            let v = Bindlib.new_var mkfree f.sym_name in
            patt_vars := StrMap.add f.sym_name v !patt_vars;
            v
        in to_var (Vari v)
    | _ -> raise Not_a_var
  in
  let replace_nl_var v =
    if VarSet.mem v !nl_vars
    then Bindlib.new_var mkfree (Bindlib.name_of v)
    else v
  in
  try
    let vs = Array.map to_var ts in
    let vs = Array.map replace_nl_var vs in
    (* We remove non-linear variables from [!patt_vars] as well. *)
    let fn n v m = if VarSet.mem v !nl_vars then m else StrMap.add n v m in
    let map = StrMap.fold fn !patt_vars StrMap.empty in
    Some (vs, map)
  with Not_a_var -> None

(** [sym_to_var m t] replaces in [t] every symbol [f] by a variable according
   to [m]. *)
let sym_to_var : tvar StrMap.t -> term -> term = fun m ->
  let rec to_var t =
    match unfold t with
    | Symb(f)     -> (try Vari (StrMap.find f.sym_name m) with Not_found -> t)
    | Prod(a,b)   -> Prod (to_var a, to_var_binder b)
    | Abst(a,b)   -> Abst (to_var a, to_var_binder b)
    | LLet(a,t,u) -> LLet (to_var a, to_var t, to_var_binder u)
    | Appl(a,b)   -> Appl(to_var a, to_var b)
    | Meta(m,ts)  -> Meta(m, Array.map to_var ts)
    | Patt(_)     -> assert false
    | TEnv(_)     -> assert false
    | TRef(_)     -> assert false
    | _           -> t
  and to_var_binder b =
    let (x,b) = Bindlib.unbind b in
    Bindlib.unbox (Bindlib.bind_var x (lift (to_var b)))
  in to_var

(** [instantiation ctx m ts u] checks whether, in a problem [m[ts]=u], [m] can
    be instantiated and returns the corresponding instantiation. It does not
    check whether the instantiation is closed though. *)
let instantiation : ctxt -> meta -> term array -> term ->
  tmbinder Bindlib.box option = fun ctx m ts u ->
  if not (occurs m u) then
    match nl_distinct_vars ctx ts with (* Theoretical justification ? *)
    | None       -> None
    | Some(vs,m) ->
        let u = if StrMap.is_empty m then u else sym_to_var m u in
        Some (Bindlib.bind_mvar vs (lift u))
  else None

(** Checking type or not during meta instanciation. *)
let do_type_check = Stdlib.ref true

(** [instantiate ctx m ts u] check whether, in a problem [m[ts]=u], [m] can be
    instantiated and, if so, instantiate it. *)
let instantiate : ctxt -> meta -> term array -> term -> constr list -> bool =
  fun ctx m ts u initial ->
  if !log_enabled then
    log_unif "try instantiate %a" pp_constr (ctx,Meta(m,ts),u);
  match instantiation ctx m ts u with
  | Some(bu) when Bindlib.is_closed bu ->
      begin
        let typ_mts =
          match Infer.type_app ctx !(m.meta_type) (Array.to_list ts) with
          | Some a -> a
          | None -> assert false
        in
        match Infer.check_noexn [] ctx u typ_mts with
        | None -> false
        | Some cs ->
            let is_initial c = List.exists (Eval.eq_constr c) initial in
            let cs = List.filter (fun c -> not (is_initial c)) cs in
            match cs <> [], Stdlib.(!do_type_check) with
            | false, _ ->
                if !log_enabled then
                  (log_unif "can instantiate (no new constraints)";
                   log_unif (yel "%a ≔ %a") pp_meta m pp_term u);
                Meta.set m (Bindlib.unbox bu); true
            | true, false ->
                if !log_enabled then
                  (log_unif "can instantiate (new constraints ignored)";
                   log_unif (yel "%a ≔ %a") pp_meta m pp_term u);
                Meta.set m (Bindlib.unbox bu); true
            | true, true ->
                if !log_enabled then
                  log_unif "cannot instantiate (new constraints)";
                false
      end
  | _ ->
      if !log_enabled then log_unif "cannot instantiate (variable condition)";
      false

(** [solve p] tries to solve the unification problem [p] and
    returns the constraints that could not be solved. *)
let rec solve : problem -> constr list = fun p ->
  if !log_enabled then log_unif "%a" pp_problem p;
  match p with
  | { to_solve = []; unsolved = []; _ } -> []
  | { to_solve = []; unsolved = cs; recompute = true } ->
     solve {empty_problem with to_solve = cs}
  | { to_solve = []; unsolved = cs; _ } -> cs
  | { to_solve = (c,t,u)::to_solve; _ } -> solve_aux c t u {p with to_solve}

and solve_aux : ctxt -> term -> term -> problem -> constr list =
  fun ctx t1 t2 p ->
  let initial = (ctx,t1,t2)::p.to_solve in
  let t1 = Eval.whnf ctx t1 in
  let t2 = Eval.whnf ctx t2 in
  let (h1, ts1) = Basics.get_args t1 in
  let (h2, ts2) = Basics.get_args t2 in
  if !log_enabled then log_unif "solve %a" pp_constr (ctx, t1, t2);

  let add_to_unsolved () =
    if Eval.eq_modulo ctx t1 t2 then solve p else
    match try_unif_rules ctx t1 t2 with
    | None     -> solve {p with unsolved = (ctx,t1,t2) :: p.unsolved}
    | Some([]) -> assert false
    (* Unification rules generate non empty list of unification constraints *)
    | Some(cs) -> solve {p with to_solve = cs @ p.to_solve}
  in

  let error () =
    fatal_msg "[%a] and [%a] are not convertible.\n"
      pp_term t1 pp_term t2;
    raise Unsolvable
  in

  let decompose () =
    if !log_enabled then log_unif "decompose";
    (* Propagate context *)
    let add_arg_pb a b l = (ctx,a,b)::l in
    let to_solve =
      (* here we use fold_right2 instead of fold_left2
         to keep the order of the decomposition
         f a b ≡ f a' b' => a ≡ a && b ≡ b' *)
      try List.fold_right2 add_arg_pb ts1 ts2 p.to_solve
      with Invalid_argument _ -> error () in
    solve {p with to_solve}
  in

  (* For a problem m[vs]=s(ts), where [vs] are distinct variables, m
     is a meta of type Πy0:a0,..,Πyk-1:ak-1,b (k = length vs), s is an
     injective symbol of type Πx0:b0,..,Πxn-1:bn-1,c (n = length ts),
     we instantiate m by s(m0[vs],..,mn-1[vs]) where mi is a fresh
     meta of type Πv0:a0,..,Πvk-1:ak-1{y0=v0,..,yk-2=vk-2},
     bi{x0=m0[vs],..,xi-1=mi-1[vs]}. *)
  let imitate_inj m vs us s ts =
    if !log_enabled then
      log_unif "imitate_inj %a ≡ %a"
        pp_term (add_args (Meta(m,vs)) us)
        pp_term (add_args (Symb s) ts);
    let exception Cannot_imitate in
    try
      if not (us = [] && is_injective s) then raise Cannot_imitate;
      let vars = match distinct_vars ctx vs with
        | None -> raise Cannot_imitate
        | Some vars -> vars
      in
      (* Build the environment (yk-1,ak-1{y0=v0,..,yk-2=vk-2});..;(y0,a0). *)
      let env, _ = Env.of_prod_using ctx vars !(m.meta_type) in
      (* Build the term s(m0[vs],..,mn-1[vs]). *)
      let k = Array.length vars in
      let t =
        let rec build i acc t =
          if i <= 0 then add_args (Symb s) (List.rev acc)
          else match unfold t with
               | Prod(a,b) ->
                  let m = Meta.fresh (Env.to_prod env (lift a)) k in
                  let u = Meta (m,vs) in
                  build (i-1) (u::acc) (Bindlib.subst b u)
               | _ -> raise Cannot_imitate
        in build (List.length ts) [] !(s.sym_type)
      in
      Meta.set m (Bindlib.unbox (Bindlib.bind_mvar vars (lift t)));
      solve { p with to_solve = (ctx,t1,t2)::p.to_solve }
    with Cannot_imitate -> add_to_unsolved ()
  in

  (* [imitate_lam_cond h ts] checks that [ts] is headed by a variable
     not occurring in [h]. *)
  let imitate_lam_cond h ts =
    match ts with
    | [] -> false
    | e :: _ ->
       begin
         match unfold e with
         | Vari x -> not (Bindlib.occur x (lift h))
         | _ -> false
       end
  in

  (* For a problem of the form Appl(m[ts],[Vari x;_])=_, where m is a
     metavariable of arity n and type Πx1:a1,..,Πxn:an,t and x does not occur
     in m[ts], instantiate m by λx1:a1,..,λxn:an,λx:a,m1[x1,..,xn,x] where
     m1 is a new metavariable of arity n+1 and:

     - either t = Πx:a,b and m1 is of type Πx1:a1,..,Πxn:an,Πx:a,b,

     - or we add the problem t = Πx:m2[x1,..,xn],m3[x1,..,xn,x] where m2 is a
     new metavariable of arity n and type Πx1:a1,..,Πxn:an,TYPE and m3 is a
     new metavariable of arity n+1 and type
     Πx1:a1,..,Πxn:an,Πx:m2[x1,..,xn],TYPE, and do as in the previous case. *)
  let imitate_lam m =
    if !log_enabled then log_unif "imitate_lam %a" pp_meta m;
    let n = m.meta_arity in
    let (env, t) = Env.of_prod ctx n !(m.meta_type) in
    let x,a,env',b,p =
      match Eval.whnf ctx t with
      | Prod(a,b) ->
         let x,b = Bindlib.unbind b in
         let a = lift a in
         let env' = Env.add x a None env in
         x,a,env',lift b,p
      | _ ->
         (* After type inference, a similar constraint should have already
            been generated but has not been processed yet. *)
         let tm2 = Env.to_prod env _Type in
         let m2 = Meta.fresh tm2 n in
         let a = _Meta m2 (Env.to_tbox env) in
         let x = Bindlib.new_var mkfree "x" in
         let env' = Env.add x a None env in
         let tm3 = Env.to_prod env' _Type in
         let m3 = Meta.fresh tm3 (n+1) in
         let b = _Meta m3 (Env.to_tbox env') in
         (* Could be optimized by extending [Env.to_tbox env]. *)
         let u = Bindlib.unbox (_Prod a (Bindlib.bind_var x b)) in
         x,a,env',b,{p with to_solve = (Env.to_ctxt env,u,t)::p.to_solve}
    in
    let tm1 = Env.to_prod env' b in
    let m1 = Meta.fresh tm1 (n+1) in
    let u1 = _Meta m1 (Env.to_tbox env') in
    let xu1 = _Abst a (Bindlib.bind_var x u1) in
    let v = Bindlib.bind_mvar (Env.vars env) xu1 in
    Meta.set m (Bindlib.unbox v);
    let t1 = add_args h1 ts1 and t2 = add_args h2 ts2 in
    solve { p with to_solve = (ctx,t1,t2)::p.to_solve }
  in

  (* [inverses_for_prod s] returns the list of triples [(s0,s1,s2,b)] such
     that [s] has a rule of the form [s(s0 l1 l2) ↪ Πx:s1(r1),s2(r2)] with
     [b=true] iff [x] occurs in [r2]. *)
  let inverses_for_prod : sym -> (sym * sym * sym * bool) list = fun s ->
    let f l rule =
      match rule.lhs with
      | [l1] ->
          begin
            match Basics.get_args l1 with
            | Symb(s0), [_;_] ->
                let n = Bindlib.mbinder_arity rule.rhs in
                begin
                  match Bindlib.msubst rule.rhs (Array.make n TE_None) with
                  | Prod (Appl (Symb(s1), _), b) ->
                      begin
                        match Bindlib.subst b Kind with
                        | Appl (Symb(s2), Appl(_,Kind)) ->
                            (s0,s1,s2,true) :: l
                        | Appl (Symb(s2), _) ->
                            (s0,s1,s2,false) :: l
                        | _ -> l
                      end
                  | _ -> l
                end
            | _, _ -> l
          end
      | _ -> l
    in
    let l = List.fold_left f [] !(s.sym_rules) in
    begin
      if !log_enabled then
        let f (s0,s1,s2,b) =
          log_unif (yel "inverses_for_prod %a: %a, %a, %a, %b")
            pp_symbol s pp_symbol s0 pp_symbol s1 pp_symbol s2 b
        in List.iter f l
    end;
    l
  in

  (* [inverse s v] computes [s^{-1}(v)], that is, a term [u] such that [s(u)]
     reduces to [v], or raises [Not_invertible]. *)
  let exception Not_invertible in

  let rec inverse s v =
    if !log_enabled then
      log_unif "inverse [%a] [%a]" pp_symbol s pp_term v;
    match Basics.get_args (Eval.whnf [] v) with
    | Symb(s'), [u] when s' == s -> u
    | Prod(a,b), _ -> find_inverse_prod a b (inverses_for_prod s)
    | _, _ -> raise Not_invertible

  and find_inverse_prod a b l =
    match l with
    | [] -> raise Not_invertible
    | (s0,s1,s2,d) :: l ->
        try inverse_prod a b s0 s1 s2 d
        with Not_invertible -> find_inverse_prod a b l

  and inverse_prod a b s0 s1 s2 d =
    let a' = inverse s1 a in
    let x,b = Bindlib.unbind b in
    let b' = lift (inverse s2 b) in
    let xb' = if d then _Abst (lift a) (Bindlib.bind_var x b') else b' in
    add_args (Symb s0) [a'; Bindlib.unbox xb']
  in

  (* [inverse_opt s ts v] returns [Some(t,s^{-1}(v))] if [ts=[t]], [s] is
     injective and [s^{-1}(v)] exists, and [None] otherwise. *)
  let inverse_opt s ts v =
    if is_injective s then
      match ts with
      | [t] -> (try Some (t, inverse s v) with Not_invertible -> None)
      | _ -> None
    else None
  in

  (* [solve_inj s ts v] tries to replace a problem of the form [s(ts) = v] by
     [t = s^{-1}(v)] when [s] is injective and [ts=[t]]. *)
  let solve_inj s ts v =
    if !log_enabled then
      log_unif "solve_inj %a ≡ %a"
        pp_term (add_args (Symb s) ts) pp_term v;
    match inverse_opt s ts v with
    | Some (a, b) -> solve { p with to_solve = (ctx,a,b)::p.to_solve }
    | None -> add_to_unsolved ()
  in

  (* For a problem of the form [m[ts] = Πx:_,_] with [ts] distinct bound
     variables, and ts1 and ts2 equal to [], [imitate_prod m ts] instantiates
     [m] by a fresh product and continue. *)
  let imitate_prod m =
    if !log_enabled then log_unif "imitate_prod %a" pp_meta m;
    let n = m.meta_arity in
    let (env, s) = Env.of_prod ctx n !(m.meta_type) in
    let xs = Array.map _Vari (vars env) in

    let t1 = to_prod env _Type in
    let m1 = Meta.fresh t1 n in

    let y = Bindlib.new_var mkfree "y" in
    let env' = add y (_Meta m1 xs) None env in
    let t2 = to_prod env' (lift s) in
    let m2 = Meta.fresh t2 (n+1) in

    let mxs = Bindlib.unbox (_Meta m xs) in
    let a = _Meta m1 xs in
    let b = Bindlib.bind_var y (_Meta m2 (Array.append xs [|_Vari y|])) in
    let prod = Bindlib.unbox (_Prod a b) in

    let ctx' = Env.to_ctxt env in
    solve { p with to_solve = (ctx',mxs,prod)::(ctx,h1,h2)::p.to_solve }
  in

  match (h1, h2) with
  (* Cases in which [ts1] and [ts2] must be empty due to typing / whnf. *)
  | (Type       , Type       )
  | (Kind       , Kind       ) -> solve p

  | (Prod(a1,b1), Prod(a2,b2))
  | (Abst(a1,b1), Abst(a2,b2)) ->
     let (x,b1,b2) = Bindlib.unbind2 b1 b2 in
     let ctx' = (x,a1,None) :: ctx in
     solve { p with to_solve = (ctx,a1,a2)::(ctx',b1,b2)::p.to_solve}

  (* Other cases. *)
  | (Vari(x1)   , Vari(x2)   ) when Bindlib.eq_vars x1 x2 -> decompose ()
  | (Symb(s1)   , Symb(s2)   ) ->
     if s1 == s2 then
       match s1.sym_prop with
       | Const
       | Injec when List.same_length ts1 ts2 -> decompose ()
       | _                                   -> add_to_unsolved ()
     else
       begin
         match s1.sym_prop, s2.sym_prop with
         | Const, Const -> error ()
         | _, _ ->
           begin
             match inverse_opt s1 ts1 t2 with
             | Some (t, u) ->
               solve { p with to_solve = (ctx,t,u)::p.to_solve }
             | None ->
               begin
                 match inverse_opt s2 ts2 t1 with
                 | Some (t, u) ->
                     solve { p with to_solve = (ctx,t,u)::p.to_solve }
                 | None -> add_to_unsolved ()
               end
           end
       end

  | (Meta(m,ts) , _          )
    when ts1 = [] && instantiate ctx m ts t2 initial ->
     solve {p with recompute = true}
  | (_          , Meta(m,ts) )
    when ts2 = [] && instantiate ctx m ts t1 initial ->
     solve {p with recompute = true}

  | (Meta(m,ts)  , Prod(_,_) )
       when ts1 = [] && instantiation ctx m ts h2 <> None -> imitate_prod m
  | (Prod(_,_)   , Meta(m,ts))
       when ts2 = [] && instantiation ctx m ts h1 <> None -> imitate_prod m

  | (Meta(m,_)  , _          ) when imitate_lam_cond h1 ts1 -> imitate_lam m
  | (_          , Meta(m,_)  ) when imitate_lam_cond h2 ts2 -> imitate_lam m

  | (Meta(m,ts) , Symb(s)    ) -> imitate_inj m ts ts1 s ts2
  | (Symb(s)    , Meta(m,ts) ) -> imitate_inj m ts ts2 s ts1

  | (Meta(_,_)  , _          )
  | (_          , Meta(_,_)  ) -> add_to_unsolved ()

  | (Symb(s)    , _          ) when not (is_constant s) -> solve_inj s ts1 t2
  | (_          , Symb(s)    ) when not (is_constant s) -> solve_inj s ts2 t1

  (* Cases of error *)
  | (Type, (Kind|Prod(_)|Symb(_)|Vari(_)|Abst(_)))
  | (Kind, (Type|Prod(_)|Symb(_)|Vari(_)|Abst(_)))
  | (Prod(_), (Type|Kind|Vari(_)|Abst(_)))
  | (Vari(_), (Type|Kind|Vari(_)|Prod(_)))
  | (Abst(_), (Type|Kind|Prod(_)))
    -> error ()

  | (_          , _          ) -> add_to_unsolved ()

(** [solve p] tries to solve the unification problem [p] and
    returns the constraints that could not be solved.
    This is the entry point setting the flag type_check *)
let solve : ?type_check:bool -> problem -> constr list =
  fun ?(type_check=true) p -> Stdlib.(do_type_check := type_check); solve p

(** [solve_noexn problem] attempts to solve [problem]. If there is
   no solution, the value [None] is returned. Otherwise [Some(cs)] is
   returned, where the list [cs] is a list of unsolved convertibility
   constraints. *)
let solve_noexn : ?type_check:bool -> problem -> constr list option =
  fun ?(type_check=true) p ->
  try Some (solve ~type_check p) with Unsolvable -> None

(** [eq_noexn c t u] tries to unify the terms [t] and [u] in context [c], by
   instantiating their metavariables. *)
let eq_noexn : ?type_check:bool -> ctxt -> term -> term -> bool =
  fun ?(type_check=true) c t u ->
  solve_noexn ~type_check {empty_problem with to_solve=[c,t,u]} = Some []
