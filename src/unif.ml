(** Solving unification constraints. *)

open Extra
open Timed
open Console
open Terms
open Basics
open Print
open Eval

(** Logging function for unification. *)
let log_solv = new_logger 's' "solv" "debugging information for unification"
let log_solv = log_solv.logger

(** Unification configuration. *)
type config =
  { symb_P     : sym (** Encoding of propositions.        *)
  ; symb_T     : sym (** Encoding of types.               *)
  ; symb_all   : sym (** Universal quantifier.            *) }

let config : config option Pervasives.ref = Pervasives.ref None

(** [set_config builtins] set the configuration from [builtins]. FIXME: add
   code to check that a config is correct. *)
let set_config : sym StrMap.t -> unit = fun builtins ->
  let open Pervasives in
  try
    let c = { symb_P   = StrMap.find "P" builtins
            ; symb_T   = StrMap.find "T" builtins
            ; symb_all = StrMap.find "all" builtins }
    in config := Some c
  with Not_found -> config := None

(** Representation of a set of problems. *)
type problems =
  { to_solve  : unif_constrs
  (** List of unification problems to solve. *)
  ; unsolved  : unif_constrs
  (** List of unification problems that could not be solved. *)
  ; recompute : bool
  (** Indicates whether unsolved problems should be rechecked. *) }

(** Type of a hypothesis on injectivity. A hypothesis (f, l) means that f is
    assumed to be I-injective i.e.,
    (ft ~ fu and ti ~ ui for all i in I) => (ti ~ ui for all i not in I)
    where I = { i | li = true }. *)
type inj_hypo = sym * bool list

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

(** [solve p hypo] tries to solve the unification problems of [p] under the
    hypothesis [hypo] and returns the constraints that could not be solved. *)
let rec solve : problems -> inj_hypo option -> unif_constrs = fun p hypo ->
  match p with
  | { to_solve = []; unsolved = []; _ } -> []
  | { to_solve = []; unsolved = cs; recompute = true } ->
     solve {no_problems with to_solve = cs} hypo
  | { to_solve = []; unsolved = cs; _ } -> cs
  | { to_solve = (t,u)::to_solve; _ } -> solve_aux t u {p with to_solve} hypo

(** [solve_aux t1 t2 p hypo] tries to solve the unificaton problem given by
    [p] and the constraint [(t1,t2)] under the hypothesis [hypo], starting
    with the latter. Note that [hypo] = None if there is no hypothesis. *)
and solve_aux : term -> term -> problems -> inj_hypo option -> unif_constrs
  = fun t1 t2 p hypo ->
  if Eval.eq_modulo t1 t2 then solve p hypo else
  let (h1, ts1) = Eval.whnf_stk t1 [] in
  let (h2, ts2) = Eval.whnf_stk t2 [] in
  if !log_enabled then
    begin
      let t1 = Eval.to_term h1 ts1 in
      let t2 = Eval.to_term h2 ts2 in
      log_solv "solve [%a] [%a]" pp t1 pp t2;
    end;

  let exception Unsolvable in

  let add_to_unsolved () =
    let t1 = Eval.to_term h1 ts1 in
    let t2 = Eval.to_term h2 ts2 in
    if Eval.eq_modulo t1 t2 then solve p hypo
    else solve {p with unsolved = (t1,t2) :: p.unsolved} hypo
  in
  let error () =
    let t1 = Eval.to_term h1 ts1 in
    let t2 = Eval.to_term h2 ts2 in
    fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2
  in
  let decompose_part bls () =
    let add_arg_pb l b (t1, t2) =
      if b then l else Pervasives.(snd !t1, snd !t2) :: l in
    let to_solve =
      try List.fold_left2 add_arg_pb p.to_solve bls (List.combine ts1 ts2)
      with Invalid_argument _ -> error () in
    solve {p with to_solve} hypo
  in
  let decompose () =
    let bls = List.map (fun _ -> false) ts1 in
    decompose_part bls ()
  in
  (* For a problem m[vs]=s(ts), where [vs] are distinct variables, m
     is a meta of type ∀y0:a0,..,∀yk-1:ak-1,b (k = length vs), s is an
     injective symbol of type ∀x0:b0,..,∀xn-1:bn-1,c (n = length ts),
     we instantiate m by s(m0[vs],..,mn-1[vs]) where mi is a fresh
     meta of type ∀v0:a0,..,∀vk-1:ak-1{y0=v0,..,yk-2=vk-2},
     bi{x0=m0[vs],..,xi-1=mi-1[vs]}. *)
  let imitate_inj m vs us s h ts =
    try
      if not (us = [] && Sign.is_inj s) then raise Unsolvable;
      let vars = match distinct_vars_opt vs with
        | None -> raise Unsolvable
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
               | _ -> raise Unsolvable
        in build (List.length ts) [] !(s.sym_type)
      in
      set_meta m (Bindlib.unbox (Bindlib.bind_mvar vars (lift t)));
      solve_aux t1 t2 p hypo
    with Unsolvable -> add_to_unsolved ()
  in

  (* [imitate_lam_cond h ts] checks that [ts] is headed by a variable
     not occurring in [h]. *)
  let imitate_lam_cond h ts =
    match ts with
    | [] -> false
    | e :: _ ->
       begin
         match unfold (snd Pervasives.(!e)) with
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
    solve_aux t1 t2 p hypo
  in

  (* [inverse c s t] computes a term [u] such that [s(u)] reduces to
     [t]. Raises [Unsolvable] if it cannot find [u]. Currently, it only
     handles the builtin [P]. *)
  let rec inverse c sym t =
    match get_args (Eval.whnf t) with
    | Symb(s,_), [u] when s == sym -> u
    | Prod(ta,b), _ when sym == c.symb_P ->
       let a = inverse c c.symb_T ta in
       let x,b' = Bindlib.unbind b in
       let b' = lift (inverse c sym b') in
       let xb' = _Abst (lift a) (Bindlib.bind_var x b') in
       add_args (symb c.symb_all) [a; Bindlib.unbox xb']
    | _ -> raise Unsolvable
  in

(* [solve_inj s ts v] tries to solve a problem of the form s(ts) = v when s is
   injective. Currently, it only handles a specific case: when s is the
   builtin P. *)
  let solve_inj s ts v =
    if !(s.sym_rules) = [] then error ()
    else
      match Pervasives.(!config) with
      | None -> add_to_unsolved ()
      | Some c ->
         try
           if s == c.symb_P then
             match ts with
             | [t] -> solve_aux Pervasives.(snd !t) (inverse c s v) p hypo
             | _ -> raise Unsolvable
           else raise Unsolvable
         with Unsolvable -> add_to_unsolved ()
  in
  match (h1, h2) with
  (* Cases in which [ts1] and [ts2] must be empty due to typing / whnf. *)
  | (Type       , Type       )
  | (Kind       , Kind       ) -> solve p hypo

  | (Prod(a1,b1), Prod(a2,b2))
  | (Abst(a1,b1), Abst(a2,b2)) ->
     let (_,b1,b2) = Bindlib.unbind2 b1 b2 in
     solve_aux a1 a2 {p with to_solve = (b1,b2) :: p.to_solve} hypo

  (* Other cases. *)
  | (Vari(x1)   , Vari(x2)   ) ->
     if Bindlib.eq_vars x1 x2 then decompose () else error ()

  | (Symb(s1,_) , Symb(s2,_) ) ->
     if s1 == s2 then
       match s1.sym_mode with
       | Const -> decompose ()
       | _     ->
           if List.same_length ts1 ts2 then
             let bls =
               List.map2
                 (fun t u ->
                   let t = snd Pervasives.(!t) in
                   let u = snd Pervasives.(!u) in
                   Eval.eq_modulo t u) ts1 ts2 in
             let check_inj_and_decompose () =
               if check_inj_sym bls s1 then decompose_part bls ()
               else add_to_unsolved () in
             match hypo with
             | None           -> check_inj_and_decompose ()
             | Some (s, bls') ->
                 if s == s1 && inj_incl bls bls' then
                   decompose_part bls ()
                 else check_inj_and_decompose ()
           else error ()
     else if !(s1.sym_rules) = [] && !(s2.sym_rules) = [] then error ()
     else add_to_unsolved ()

  | (Meta(m,ts) , _          ) when ts1 = [] && instantiate m ts t2 ->
     solve {p with recompute = true} hypo
  | (_          , Meta(m,ts) ) when ts2 = [] && instantiate m ts t1 ->
     solve {p with recompute = true} hypo

  | (Meta(m,_)  , _          ) when imitate_lam_cond h1 ts1 -> imitate_lam m
  | (_          , Meta(m,_)  ) when imitate_lam_cond h2 ts2 -> imitate_lam m

  | (Meta(m,ts) , Symb(s,h)  ) -> imitate_inj m ts ts1 s h ts2
  | (Symb(s,h)  , Meta(m,ts) ) -> imitate_inj m ts ts2 s h ts1

  | (Meta(_,_)  , _          )
  | (_          , Meta(_,_)  ) -> add_to_unsolved ()

  | (Symb(s,_)  , _          ) -> solve_inj s ts1 t2
  | (_          , Symb(s,_)  ) -> solve_inj s ts2 t1

  | (_          , _          ) -> error ()

(** The following functions are used to determine whether a function symbol
    f is I-injective (I is a subset of {1, ..., n} where n is the arity of
    f).
    A function symbol f is said to be I-injective if
    ( f t1 ... tn ~ f u1 ... un and ti ~ ui for all i in I ) implies
    ( ti ~ ui for all i not in I. ). In the following, I is represented by
    a list of boolean values [b1; ...; bn] such that bi is true iff i is in
    I. *)

(** Intuitively, we want to prove the I-injectivity of f by well-founded
    induction. Let > be the union of subterm relation and the reduction.
    We prove [(f t1 ... tn ~ f u1 ... un and ti ~ ui for all i in I) =>
    (ti ~ ui for all i)] by induction using >_seq on (ft1...tn, fu1...un).
    Consider ft ~ fu where t = t1...tn and u = u1...un. We write t ~ u if
    ti ~ ui for all i.
    We distinguish three cases:
    - ft and fu are in normal form : Then ft = fu and t = u.
    - ft is in normal form and there exists v s.t. fu -> v.
      Suppose that there exists k and uk' s.t. uk -> uk'. We have fu -> fu'
      (and thus (ft, fu) >_seq (ft, fu') where u' = u1...uk'...un and it is
      clear that ti ~ (u')i for all i in I.
      Hence by applying the induction hypothesis, ti ~ (u')i and thus ti ~ ui
      for all i in I.
      Suppose that ui are all in normal form. Then there exists a rule R such
      that fu ->_R v by applying R at the root.
      We do not have a general solution in this case now but we could give
      some sufficient conditions for dealing with this case.
      - If a rule R' is of the form fl -> sr where s is a constant symbol,
        then R cannot be R'.
        In fact, if R = R' then ft, the normal form of v, is
        headed by s, which is impossible.
      - If a rule R' is of the form fl -> x s.t. li = x for some i in I,
        then R cannot be R'.
        In fact, if R = R' then v = ui ~ ti by hypothesis. We have also
        v ~ ft. Since ti and ft are in normal form, ti = ft, which is
        impossible since ti is a proper subterm of ft.
      Hence, if all the rules are in one of the above forms, then there is no
      need to deal with this case.
    - There exist v and w such that ft -> v and fu -> w.
      If there exist k and tk' (resp. uk') s.t. tk -> tk' (resp. uk -> uk'),
      then by applying the induction hypothesis, ti ~ ui for all i.
      Suppose that ti and ui are all in normal form. There exist thus two
      rules (not nessarily distinct) R1 and R2 s.t. ft ->_R1 v and fu ->_R2 w
      by applying R1 and R2 at the roots.
      In this case, we suppose R1 = fl1 -> r1 and R2 = fl2 -> r2. There exist
      therefore two substitutions σ1 and σ2 s.t. ft = fl1σ1 and fu = fl2σ2.
      Let σ be the union of σ1 and σ2.
      We now attempt to unify (r, r') and ((l1)i, (l2)i) for all i in I.
      During this unification procedure, we use the hypothesis that f is
      I-injective, which is justified by the following property:
      whenever we unify (r, s), if ft' (resp. fu') is a subterm of r (resp. s)
      then there exists t'' (resp. u'') s.t. ft'' < ft and t'σ ->* t''
      (resp. fu'' < fu and u'σ ->* u'').
      Proof sketch:
      By induction on the unification steps.
      Initially, the property is clearly verified since v < t (resp. w < u)
      and ti < t (resp. ui < u).
      The only induction step that needs to be checked is the instantiation of
      a metavariable.
      After instantiating a metavariable m with a term s, every pair
      (ft', fu') becomes (ft'[m <- s], fu'[m <- s]).
      By I.H., there exist t'' and u'' s.t. ft'' < ft, fu'' < fu, t'σ ->* t''
      and u'σ ->* u''.
      Let σ' be the restriction of σ to dom(σ)\{m}.
      We have thus t'σ = t'σ'[m <- mσ] and t'[m <- s]σ = t'σ'[m <- sσ]
      (similarly for u'σ and u'[m <- s]σ). mσ is in normal form since it
      is a subterm of t, which is itself in normal form.
      We know that the unification (m, s) implicitly means that mσ ~ sσ and
      thus sσ ->* mσ. Therefore, t'[m <- s]σ ->* t'σ ->* t'' and
      u'[m <- s]σ ->* u'σ -> u''.
      Therefore, when we unify (ft', fu'), if (t')i ~ (u')i for all i in I,
      then we can remove this pair from the problem and add the pairs
      {((t')i, (u')i), i in I}.
      After unifying (r, r') and ((l1)i, (l2)i) for all i in I, we attempt to
      unify ((l1)i, (l2)i) for all i not in I and use the constraints deduced
      in the previous part to solve the constraints obtained in this part.
      If both parts of unification succeed or the first part fails, then we
      say that this pair of rules (R_1, R_2) is "good".

    Our algorithm consists of checking that every pair of rules is good and
    that every rule is in one of the forms mentioned in the second case. *)

(** [inj_incl bls bls'] checks if bls'_i => bls_i for all i. This
    corresponds to the property that I-injectivity implies J-injectivity if I
    is included in J. *)
and inj_incl : bool list -> bool list -> bool = fun bls bls' ->
  List.for_all2 (fun b b' -> b || not b') bls bls'

(** [inj_incls bls blss] checks if there exists [bls'] in [blss] such that
    bls'_i => bls_i for all i. *)
and inj_incls : bool list -> bool list list -> bool = fun bls blss ->
  List.exists (fun bls' -> inj_incl bls bls') blss

(** [eq_modulo_constrs constrs (t1, t2)] returns if t1 ~ t2 or there exists
    (t1', t2') in [constrs] such that t1 ~ t1' (resp. t2') and t2 ~ t2'
    (resp. t1'). *)
and eq_modulo_constrs : unif_constrs -> term * term -> bool
  = fun constrs (t1, t2) ->
  let fn (t1', t2') =
    (eq_modulo t1 t1' && eq_modulo t2 t2') ||
    (eq_modulo t1 t2' && eq_modulo t2 t1') in
  eq_modulo t1 t2 || List.exists fn constrs

(** [add_rules_from_constrs constrs] first replaces each metavariable in
    [constrs] with a fresh symbol, then applies the completion procedure on
    the first-order constraints in [constrs]. *)
and add_rules_from_constrs : unif_constrs -> unit = fun constrs ->
  let fn m =
    match !(m.meta_value) with
    | None   ->
        let n = string_of_int m.meta_key in
        let term_t_m = !(m.meta_type) in
        let c_m = new_symb ("{c_" ^ n) term_t_m in
        if m.meta_arity <> 0 then raise Non_nullary_meta;
        m.meta_value :=
          Some (Bindlib.unbox (Bindlib.bind_mvar [||] (_Symb c_m Nothing)))
    | Some _ -> () in
  let fo_constrs fo (t, u) =
    try
      check_nullary_meta t;
      check_nullary_meta u;
      iter_meta fn t;
      iter_meta fn u;
      (t, u) :: fo
    with Non_nullary_meta -> fo in
  let constrs_fo = List.fold_left fo_constrs [] constrs in
  let t1 = Time.save () in
  let ord = Completion.ord_from_eqs constrs_fo in
  let rules_to_add = Completion.completion constrs_fo ord in
  Time.restore t1;
  List.iter
    (fun (s, rs) -> s.sym_rules := rs @ !(s.sym_rules)) rules_to_add

(** [check_pair_of_rules bls (lhs1, rhs1) (lhs2, rhs2)] checks if
    the rules [lhs1 -> rhs1] and [lhs2 -> rhs2] satisfy the conditions
    mentioned above. *)
and check_pair_of_rules :
  bool list -> sym -> term * term -> term * term -> bool
  = fun bls s (lhs1, rhs1) (lhs2, rhs2) ->
  let t = Time.save () in
  try
    let _, args1 = get_args lhs1 in
    let _, args2 = get_args lhs2 in
    let args = List.combine args1 args2 in
    let to_solve =
      (rhs1, rhs2) :: List.map snd (List.filter fst (List.combine bls args))
    in
    let constrs = solve {no_problems with to_solve} (Some (s, bls)) in
    let to_solve =
      List.map
        snd (List.filter (fun (b, _) -> not b) (List.combine bls args)) in
    add_rules_from_constrs constrs;
    let res =
      List.for_all (eq_modulo_constrs constrs) to_solve in
    Time.restore t;
    res
  with
  | Fatal _ -> Time.restore t; true
  | _       -> Time.restore t; false

(** [non_erasing_rec s] returns true if the normal form of any term [st] is
    of the form [s't'] with s' <= s. This function only makes sense when there
    is an order on symbols compatible with their dependency. *)
and non_erasing_rec : sym -> bool = fun s ->
  let check_head_of_rule : rule -> bool = fun r ->
    let h, _ = get_args (term_of_rhs r) in
    match h with
    | Symb (s', _) -> s' == s || non_erasing_rec s
    | _            -> false in
  List.for_all check_head_of_rule !(s.sym_rules)

(** [check_single_rule bls s (lhs, rhs)] checks if the rule [lhs -> rhs]
    satisfies the conditions mentioned above. *)
and check_single_rule : bool list -> sym -> term * term -> bool
  = fun bls s (lhs, rhs) ->
  let t = Time.save () in
  let new_args n =
    List.init n (fun _ -> (Meta (fresh_meta Kind 0, [||]))) in
  let h1, args1 = get_args rhs in
  let _, args2 = get_args lhs in
  let new_args = new_args (List.length args2) in
  let argss = List.combine args2 new_args in
  let new_term = add_args (Symb (s, Nothing)) new_args in
  let infer_from_constrs () =
    let to_solve =
      (new_term, rhs) ::
      List.map snd (List.filter fst (List.combine bls argss)) in
    let constrs = solve {no_problems with to_solve} (Some (s, bls)) in
    let to_solve =
      List.map
        snd (List.filter (fun (b, _) -> not b) (List.combine bls argss))
    in
    add_rules_from_constrs constrs;
    let res =
      List.for_all (eq_modulo_constrs constrs) to_solve in
    Time.restore t;
    res
  in
  try match h1 with
    | Meta (m, _) when args1 = [] ->
        let fn = function
          | Meta (m', _) -> m == m'
          | _            -> false in
        if List.exists2 (fun b arg -> b && fn arg) bls args2 then true
        else infer_from_constrs ()
    | Symb (s', _) when s == s'   -> infer_from_constrs ()
    | Symb (s', _)                -> non_erasing_rec s'
    | _                           -> false (* TODO *)
  with
  | Fatal _ -> Time.restore t; true
  | _       -> Time.restore t; false

(** [check_inj_sym bls s] checks if the symbol [s] is I-injective, where
    I is represented by [bls]. Note that this function gives only a
    sufficient condition. It may returns false whereas [s] is I-injective. *)
and check_inj_sym : bool list -> sym -> bool = fun bls s ->
  match s.sym_mode with
  | Injec l when inj_incls bls l -> true
  | _                             ->
      let rules = !(s.sym_rules) in
      let terms_of_rules =
        List.map (fun r -> replace_patt_by_meta_rule (s, r)) rules in
      let rec check_inj_rules : (term * term) list -> bool = function
        | []       -> true
        | r :: rs' ->
            check_inj_rules rs' &&
            check_pair_of_rules bls s r (copy_rule r) &&
            List.fold_left
              (fun acc r' -> acc && check_pair_of_rules bls s r r')
              true rs' in
      List.for_all (check_single_rule bls s) terms_of_rules &&
      check_inj_rules terms_of_rules

(** [solve builtins flag problems] attempts to solve [problems], after having
   sets the value of [can_instantiate] to [flag].  If there is no solution,
   the value [None] is returned. Otherwise [Some(cs)] is returned, where the
   list [cs] is a list of unsolved convertibility constraints. *)
let solve : sym StrMap.t -> bool -> problems -> unif_constrs option =
  fun builtins b p ->
  set_config builtins;
  can_instantiate := b;
  try Some (solve p None) with Fatal(_,m) ->
    if !log_enabled then log_solv (red "solve: %s") m; None
