(** Solving unification constraints. *)

open Extra
open Timed
open Console
open Terms
open Basics
open Env

(** Logging function for unification. *)
let log_unif = new_logger 'u' "unif" "unification"
let log_unif = log_unif.logger

(** Exception raised when a constraint is not solvable. *)
exception Unsolvable

(** [copy_prod_env xs prod] constructs an environment mapping the variables of
    [xs] to successive dependent product type domains of the term [prod]. Note
    that dependencies are preserved in the process,  and types of the produced
    environment can hence refer to other variables of the environment whenever
    this is necessary. Note that the produced environment is equivalent to the
    environment [fst (destruct_prod (Array,length xs) prod)] if the variables
    of its domain are substituted by those of [xs]. Intuitively,  if [prod] is
    of the form [∀ (y1:a1) ⋯ (yn:an), a]  then the environment returned by the
    function is (roughly) [(xn, an{y1≔x1, ⋯, yn-1≔xn-1}) ; ⋯ ; (x1, a1)]. Note
    that the function raises [Invalid_argument] if [prod] does not evaluate to
    a sequence of [Array.length xs] dependent products. *)
let copy_prod_env : tvar array -> term -> env = fun xs t ->
  let n = Array.length xs in
  let rec build_env i env t =
    if i >= n then env else
    match Eval.whnf [] t with
    | Prod(a,b) -> let env = add xs.(i) (lift a) None env in
                   build_env (i+1) env (Bindlib.subst b (Vari(xs.(i))))
    | _         -> invalid_arg "of_prod_vars"
  in
  build_env 0 [] t

(** [nl_distinct_vars ctx ts] checks that [ts] is made of variables  [vs] only
    and returns some copy of [vs] where variables occurring more than once are
    replaced by fresh variables.  Variables defined in  [ctx] are unfolded. It
    returns [None] otherwise. *)
let nl_distinct_vars
    : ctxt -> term array -> (tvar array * tvar StrMap.t) option
  = fun ctx ts ->
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
    | Symb(f) when f.sym_name <> "" && f.sym_name.[0] = '&' ->
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

(** [instantiate ctx m ts u] check whether, in a problem [m[ts]=u], [m] can be
    instantiated and, if so, instantiate it. *)
let instantiate : ctxt -> meta -> term array -> term -> bool =
  fun ctx m ts u ->
  match instantiation ctx m ts u with
  | Some(bu) when Bindlib.is_closed bu ->
      if !log_enabled then
        log_unif (yel "%a ≔ %a") Print.meta m Print.term u;
      set_meta m (Bindlib.unbox bu); true
  | _ -> false

(** [solve cfg p] tries to solve the unification problem [p] and
    returns the constraints that could not be solved. *)
let rec solve : problem -> constr list = fun p ->
  match p with
  | { to_solve = []; unsolved = []; _ } -> []
  | { to_solve = []; unsolved = cs; recompute = true } ->
     solve {empty_problem with to_solve = cs}
  | { to_solve = []; unsolved = cs; _ } -> cs
  | { to_solve = (c,t,u)::to_solve; _ } -> solve_aux c t u {p with to_solve}

(** [solve_aux t1 t2 p] tries to solve the unificaton problem given by [p] and
    the constraint [(t1,t2)], starting with the latter. *)
and solve_aux : ctxt -> term -> term -> problem -> constr list =
  fun ctx t1 t2 p ->
  let t1 = Eval.whnf ctx t1 in
  let t2 = Eval.whnf ctx t2 in
  let (h1, ts1) = Basics.get_args t1 in
  let (h2, ts2) = Basics.get_args t2 in
  if !log_enabled then log_unif "solve %a" Print.constr (ctx, t1, t2);

  let add_to_unsolved () =
    if Eval.eq_modulo ctx t1 t2 then solve p else
    (* Keep the context *)
    solve {p with unsolved = (ctx,t1,t2) :: p.unsolved}
  in

  let error () =
    fatal_msg "[%a] and [%a] are not convertible.\n"
      Print.term t1 Print.term t2;
    raise Unsolvable
  in

  let decompose () =
    (* Propagate context *)
    let add_arg_pb l a b = (ctx,a,b)::l in
    let to_solve =
      try List.fold_left2 add_arg_pb p.to_solve ts1 ts2
      with Invalid_argument _ -> error () in
    solve {p with to_solve}
  in

  (* For a problem m[vs]=s(ts), where [vs] are distinct variables, m
     is a meta of type ∀y0:a0,..,∀yk-1:ak-1,b (k = length vs), s is an
     injective symbol of type ∀x0:b0,..,∀xn-1:bn-1,c (n = length ts),
     we instantiate m by s(m0[vs],..,mn-1[vs]) where mi is a fresh
     meta of type ∀v0:a0,..,∀vk-1:ak-1{y0=v0,..,yk-2=vk-2},
     bi{x0=m0[vs],..,xi-1=mi-1[vs]}. *)
  let imitate_inj m vs us s ts =
    if !log_enabled then
      log_unif "imitate_inj %a ≡ %a"
        Print.term (add_args (Meta(m,vs)) us)
        Print.term (add_args (Symb s) ts);
    let exception Cannot_imitate in
    try
      if not (us = [] && is_injective s) then raise Cannot_imitate;
      let vars = match distinct_vars ctx vs with
        | None -> raise Cannot_imitate
        | Some vars -> vars
      in
      (* Build the environment (yk-1,ak-1{y0=v0,..,yk-2=vk-2});..;(y0,a0). *)
      let env = copy_prod_env vars !(m.meta_type) in
      (* Build the term s(m0[vs],..,mn-1[vs]). *)
      let k = Array.length vars in
      let t =
        let rec build i acc t =
          if i <= 0 then add_args (Symb s) (List.rev acc)
          else match unfold t with
               | Prod(a,b) ->
                  let m = fresh_meta (Env.to_prod env (lift a)) k in
                  let u = Meta (m,vs) in
                  build (i-1) (u::acc) (Bindlib.subst b u)
               | _ -> raise Cannot_imitate
        in build (List.length ts) [] !(s.sym_type)
      in
      set_meta m (Bindlib.unbox (Bindlib.bind_mvar vars (lift t)));
      solve_aux ctx t1 t2 p
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
     metavariable of arity n and type ∀x1:a1,..,∀xn:an,t and x does not occur
     in m[ts], instantiate m by λx1:a1,..,λxn:an,λx:a,m1[x1,..,xn,x] where
     m1 is a new metavariable of arity n+1 and:

     - either t = ∀x:a,b and m1 is of type ∀x1:a1,..,∀xn:an,∀x:a,b,

     - or we add the problem t = ∀x:m2[x1,..,xn],m3[x1,..,xn,x] where m2 is a
     new metavariable of arity n and type ∀x1:a1,..,∀xn:an,KIND and m3 is a
     new metavariable of arity n+1 and type
     ∀x1:a1,..,∀xn:an,∀x:m2[x1,..,xn],KIND, and do as in the previous case. *)
  let imitate_lam m =
    let n = m.meta_arity in
    let (env, t) = Infer.destruct_prod n !(m.meta_type) in
    let x,a,env',b,p =
      match Eval.whnf [] t with
      | Prod(a,b) ->
         let x,b = Bindlib.unbind b in
         let a = lift a in
         let env' = Env.add x a None env in
         x,a,env',lift b,p
      | _ ->
         (* After type inference, a similar constraint should have already
            been generated but has not been processed yet. *)
         let tm2 = Env.to_prod env _Kind in
         let m2 = fresh_meta tm2 n in
         let a = _Meta m2 (Env.to_tbox env) in
         let x = Bindlib.new_var mkfree "x" in
         let env' = Env.add x a None env in
         let tm3 = Env.to_prod env' _Kind in
         let m3 = fresh_meta tm3 (n+1) in
         let b = _Meta m3 (Env.to_tbox env') in
         (* Could be optimized by extending [Env.to_tbox env]. *)
         let u = Bindlib.unbox (_Prod a (Bindlib.bind_var x b)) in
         x,a,env',b,{p with to_solve = (ctx,u,t)::p.to_solve}
    in
    let tm1 = Env.to_prod env' b in
    let m1 = fresh_meta tm1 (n+1) in
    let u1 = _Meta m1 (Env.to_tbox env') in
    let xu1 = _Abst a (Bindlib.bind_var x u1) in
    let v = Bindlib.bind_mvar (Env.vars env) xu1 in
    set_meta m (Bindlib.unbox v);
    let t1 = add_args h1 ts1 and t2 = add_args h2 ts2 in
    solve_aux ctx t1 t2 p
  in

  (* [inverses_for_prod s] returns the list of triples [(s0,s1,s2,b)] such
     that [s] has a rule of the form [s(s0 l1 l2) → ∀x:s1(r1),s2(r2)] with
     [b=true] iff [x] occurs in [r2]. *)
  let inverses_for_prod : sym -> (sym * sym * sym * bool) list = fun s ->
    let f l rule =
      match rule.lhs with
      | [l1] ->
          begin
            match get_args l1 with
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
            Print.symbol s Print.symbol s0 Print.symbol s1 Print.symbol s2 b
        in List.iter f l
    end;
    l
  in

  (* [inverse s v] computes [s^{-1}(v)], that is, a term [u] such that [s(u)]
     reduces to [v], or raises [Not_invertible]. *)
  let exception Not_invertible in

  let rec inverse s v =
    if !log_enabled then
      log_unif "inverse [%a] [%a]" Print.symbol s Print.term v;
    match get_args (Eval.whnf [] v) with
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
        Print.term (add_args (Symb s) ts) Print.term v;
    match inverse_opt s ts v with
    | Some (a, b) -> solve_aux ctx a b p
    | None -> add_to_unsolved ()
  in

  (* For a problem of the form [m[ts] = ∀x:_,_] with [ts] distinct bound
     variables, [imitate_prod m ts] instantiates [m] by a fresh product and
     continue. *)
  let imitate_prod m =
    let mxs, prod, _, _ = Infer.extend_meta_type m in
    (* ts1 and ts2 are equal to [] *)
    solve_aux ctx mxs prod { p with to_solve = (ctx,h1,h2)::p.to_solve }
  in

  match (h1, h2) with
  (* Cases in which [ts1] and [ts2] must be empty due to typing / whnf. *)
  | (Type       , Type       )
  | (Kind       , Kind       ) -> solve p

  | (Prod(a1,b1), Prod(a2,b2))
  | (Abst(a1,b1), Abst(a2,b2)) ->
     let (_,b1,b2) = Bindlib.unbind2 b1 b2 in
     solve_aux ctx a1 a2 {p with to_solve = (ctx,b1,b2) :: p.to_solve}

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
             | Some (t, u) -> solve_aux ctx t u p
             | None ->
               begin
                 match inverse_opt s2 ts2 t1 with
                 | Some (t, u) -> solve_aux ctx t u p
                 | None -> add_to_unsolved ()
               end
           end
       end

  | (Meta(m,ts) , _          ) when ts1 = [] && instantiate ctx m ts t2 ->
     solve {p with recompute = true}
  | (_          , Meta(m,ts) ) when ts2 = [] && instantiate ctx m ts t1 ->
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

(** [solve builtins flag problem] attempts to solve [problem]. If there is
   no solution, the value [None] is returned. Otherwise [Some(cs)] is
   returned, where the list [cs] is a list of unsolved convertibility
   constraints. *)
let solve : Builtin.map -> problem -> constr list option =
  fun _builtins p ->
  try Some (solve p) with Unsolvable -> None
