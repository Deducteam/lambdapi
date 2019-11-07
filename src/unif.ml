(** Solving unification constraints. *)

open Extra
open Timed
open Console
open Terms
open Basics
open Print

(** Logging function for unification. *)
let log_unif = new_logger 'u' "unif" "unification"
let log_unif = log_unif.logger

(** Exception raised when a constraint is not solvable. *)
exception Unsolvable

(** Representation of a set of problems. *)
type problems =
  { to_solve  : unif_constrs
  (** List of unification problems to solve. *)
  ; unsolved  : unif_constrs
  (** List of unification problems that could not be solved. *)
  ; recompute : bool
  (** Indicates whether unsolved problems should be rechecked. *) }

(** Empty problem. *)
let no_problems : problems =
  {to_solve  = []; unsolved = []; recompute = false}

(** Boolean saying whether user metavariables can be set or not. *)
let can_instantiate : bool ref = ref true

(** [nl_distinct_vars ts] checks that [ts] is made of variables [vs] only
   and returns some copy of [vs] where variables occurring more than
   once are replaced by fresh variables. It returns [None]
   otherwise. *)
let nl_distinct_vars : term array -> tvar array option =
  let exception Not_a_var in fun ts ->
  let open Pervasives in
  let vars = ref VarSet.empty
  and nl_vars = ref VarSet.empty in
  let to_var t =
    match unfold t with
    | Vari x ->
       begin
         if VarSet.mem x !vars then nl_vars := VarSet.add x !nl_vars
         else vars := VarSet.add x !vars;
         x
       end
    | _ -> raise Not_a_var
  in
  let replace_nl_var x =
    if VarSet.mem x !nl_vars then Bindlib.new_var mkfree "_" else x
  in
  try Some (Array.map replace_nl_var (Array.map to_var ts))
  with Not_a_var -> None

(** [instantiate m ts u] check whether [m] can be instantiated for solving the
    unification problem “m[ts] = u”. The returned boolean tells whether [m]
    was instantiated or not. *)
let instantiate : meta -> term array -> term -> bool = fun m ts u ->
  (!can_instantiate || internal m)
  && not (occurs m u)
  && match nl_distinct_vars ts with
     | None -> false
     | Some vs ->
        let bu = Bindlib.bind_mvar vs (lift u) in
        Bindlib.is_closed bu (* To make sure that there is no non-linear
                                variable of [vs] occurring in [u]. *)
        && (set_meta m (Bindlib.unbox bu); true)

(** [solve cfg p] tries to solve the unification problems of [p] and
   returns the constraints that could not be solved. *)
let rec solve : problems -> unif_constrs = fun p ->
  match p with
  | { to_solve = []; unsolved = []; _ } -> []
  | { to_solve = []; unsolved = cs; recompute = true } ->
     solve {no_problems with to_solve = cs}
  | { to_solve = []; unsolved = cs; _ } -> cs
  | { to_solve = (t,u)::to_solve; _ } -> solve_aux t u {p with to_solve}

(** [solve_aux t1 t2 p] tries to solve the unificaton problem given by [p] and
    the constraint [(t1,t2)], starting with the latter. *)
and solve_aux : term -> term -> problems -> unif_constrs = fun t1 t2 p ->
  let (h1, ts1) = Eval.whnf_stk t1 [] in
  let (h2, ts2) = Eval.whnf_stk t2 [] in
  if !log_enabled then
    begin
      let t1 = add_args h1 ts1 in
      let t2 = add_args h2 ts2 in
      log_unif "unify [%a] [%a]" pp t1 pp t2;
    end;

  let add_to_unsolved () =
    let t1 = add_args h1 ts1 in
    let t2 = add_args h2 ts2 in
    if Eval.eq_modulo t1 t2 then solve p
    else solve {p with unsolved = (t1,t2) :: p.unsolved}
  in

  let error () =
    let t1 = add_args h1 ts1 in
    let t2 = add_args h2 ts2 in
    fatal_msg "[%a] and [%a] are not convertible.\n" pp t1 pp t2;
    raise Unsolvable
  in

  let decompose () =
    let add_arg_pb l t1 t2 = (t1, t2)::l in
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
  let imitate_inj m vs us s h ts =
    let exception Cannot_imitate in
    try
      if not (us = [] && is_inj s) then raise Cannot_imitate;
      let vars = match distinct_vars_opt vs with
        | None -> raise Cannot_imitate
        | Some vars -> vars
      in
      (* Build the environment (yk-1,ak-1{y0=v0,..,yk-2=vk-2});..;(y0,a0). *)
      let env, _ = Env.of_prod_vars vars !(m.meta_type) in
      (* Build the term s(m0[vs],..,mn-1[vs]). *)
      let k = Array.length vars in
      let t =
        let rec build i acc t =
          if i <= 0 then Basics.add_args (Symb(s,h)) (List.rev acc)
          else match unfold t with
               | Prod(a,b) ->
                  let m = fresh_meta (Env.to_prod env (lift a)) k in
                  let u = Meta (m,vs) in
                  build (i-1) (u::acc) (Bindlib.subst b u)
               | _ -> raise Cannot_imitate
        in build (List.length ts) [] !(s.sym_type)
      in
      set_meta m (Bindlib.unbox (Bindlib.bind_mvar vars (lift t)));
      solve_aux t1 t2 p
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
    let env, t = Env.of_prod_arity n !(m.meta_type) in
    let x,a,env',b,p =
      match Eval.whnf t with
      | Prod(a,b) ->
         let x,b = Bindlib.unbind b in
         let a = lift a in
         let env' = Env.add x a env in
         x,a,env',lift b,p
      | _ ->
         (* After type inference, a similar constraint should have already
            been generated but has not been processed yet. *)
         let t2 = Env.to_prod env _Kind in
         let m2 = fresh_meta t2 n in
         let a = _Meta m2 (Env.to_tbox env) in
         let x = Bindlib.new_var mkfree "x" in
         let env' = Env.add x a env in
         let t3 = Env.to_prod env' _Kind in
         let m3 = fresh_meta t3 (n+1) in
         let b = _Meta m3 (Env.to_tbox env') in
         (* Could be optimized by extending [Env.to_tbox env]. *)
         let u = Bindlib.unbox (_Prod a (Bindlib.bind_var x b)) in
         x,a,env',b,{p with to_solve = (u,t)::p.to_solve}
    in
    let tm1 = Env.to_prod env' b in
    let m1 = fresh_meta tm1 (n+1) in
    let u1 = _Meta m1 (Env.to_tbox env') in
    let xu1 = _Abst a (Bindlib.bind_var x u1) in
    let v = Bindlib.bind_mvar (Env.vars env) xu1 in
    set_meta m (Bindlib.unbox v);
    solve_aux t1 t2 p
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
            | Symb(s0,_), [_;_] ->
                let n = Bindlib.mbinder_arity rule.rhs in
                begin
                  match Bindlib.msubst rule.rhs (Array.make n TE_None) with
                  | Prod (Appl (Symb(s1,_), _), b) ->
                      begin
                        match Bindlib.subst b Kind with
                        | Appl (Symb(s2,_), Appl(_,Kind)) ->
                            (s0,s1,s2,true) :: l
                        | Appl (Symb(s2,_), _) ->
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
            pp (symb s) pp (symb s0) pp (symb s1) pp (symb s2) b
        in List.iter f l
    end;
    l
  in

  (* [inverse s v] computes [s^{-1}(v)], that is, a term [u] such that [s(u)]
     reduces to [v], or raises [Not_invertible]. *)
  let exception Not_invertible in

  let rec inverse s v =
    if !log_enabled then log_unif "inverse [%a] [%a]" pp (symb s) pp v;
    match get_args (Eval.whnf v) with
    | Symb(s',_), [u] when s' == s -> u
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
    add_args (symb s0) [a'; Bindlib.unbox xb']
  in

  (* [inverse_opt s ts v] returns [Some(t,s^{-1}(v))] if [ts=[t]], [s] is
     injective and [s^{-1}(v)] exists, and [None] otherwise. *)
  let inverse_opt s ts v =
    if s.sym_mode = Injec then
      match ts with
      | [t] -> begin try Some (t, inverse s v) with Not_invertible -> None end
      | _ -> None
    else None
  in

  (* [solve_inj s ts v] tries to replace a problem of the form [s(ts) = v] by
     [t = s^{-1}(v)] when [s] is injective and [ts=[t]]. *)
  let solve_inj s ts v =
    if !(s.sym_rules) = [] then error ()
    else match inverse_opt s ts v with
         | Some (t1, s_1_v) -> solve_aux t1 s_1_v p
         | None -> add_to_unsolved ()
  in

  match (h1, h2) with
  (* Cases in which [ts1] and [ts2] must be empty due to typing / whnf. *)
  | (Type       , Type       )
  | (Kind       , Kind       ) -> solve p

  | (Prod(a1,b1), Prod(a2,b2))
  | (Abst(a1,b1), Abst(a2,b2)) ->
     let (_,b1,b2) = Bindlib.unbind2 b1 b2 in
     solve_aux a1 a2 {p with to_solve = (b1,b2) :: p.to_solve}

  (* Other cases. *)
  | (Vari(x1)   , Vari(x2)   ) ->
     if Bindlib.eq_vars x1 x2 then decompose () else error ()

  | (Symb(s1,_) , Symb(s2,_) ) ->
     if s1 == s2 then
       match s1.sym_mode with
       | Const -> decompose ()
       | Injec ->
          if List.same_length ts1 ts2 then decompose ()
          else if !(s1.sym_rules) = [] then error ()
          else add_to_unsolved ()
       | Defin ->
          if !(s1.sym_rules) <> [] || List.same_length ts1 ts2
          then add_to_unsolved ()
          else error ()
       | Priva -> failwith "implement me"
     else if !(s1.sym_rules) = [] then solve_inj s2 ts2 t1
     else if !(s2.sym_rules) = [] then solve_inj s1 ts1 t2
     else
       begin
         match inverse_opt s1 ts1 t2 with
         | Some (t, u) -> solve_aux t u p
         | None ->
             match inverse_opt s2 ts2 t1 with
             | Some (t, u) -> solve_aux t u p
             | None -> add_to_unsolved ()
       end

  | (Meta(m,ts) , _          ) when ts1 = [] && instantiate m ts t2 ->
     solve {p with recompute = true}
  | (_          , Meta(m,ts) ) when ts2 = [] && instantiate m ts t1 ->
     solve {p with recompute = true}

  | (Meta(m,_)  , _          ) when imitate_lam_cond h1 ts1 -> imitate_lam m
  | (_          , Meta(m,_)  ) when imitate_lam_cond h2 ts2 -> imitate_lam m

  | (Meta(m,ts) , Symb(s,h)  ) -> imitate_inj m ts ts1 s h ts2
  | (Symb(s,h)  , Meta(m,ts) ) -> imitate_inj m ts ts2 s h ts1

  | (Meta(_,_)  , _          )
  | (_          , Meta(_,_)  ) -> add_to_unsolved ()

  | (Symb(s,_)  , _          ) -> solve_inj s ts1 t2
  | (_          , Symb(s,_)  ) -> solve_inj s ts2 t1

  | (_          , _          ) -> error ()

(** [solve builtins flag problems] attempts to solve [problems], after having
   sets the value of [can_instantiate] to [flag].  If there is no solution,
   the value [None] is returned. Otherwise [Some(cs)] is returned, where the
   list [cs] is a list of unsolved convertibility constraints. *)
let solve : sym StrMap.t -> bool -> problems -> unif_constrs option =
  fun _builtins b p ->
  can_instantiate := b;
  try Some (solve p) with Unsolvable -> None
