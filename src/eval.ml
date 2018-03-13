(** Evaluation and conversion. *)

open Extra
open Console
open Terms
open Print

(** [eq t u] tests the equality of the two terms [t] and [u]. Note
    that during the comparison, unification variables may be
    instantiated. *)
let eq : term -> term -> bool = fun a b ->
  let rec eq a b = a == b ||
    let eq_binder = Bindlib.eq_binder mkfree eq in
    match (unfold a, unfold b) with
    | (Vari(x1)     , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Symb(Sym(s1)), Symb(Sym(s2))) -> s1 == s2
    | (Symb(Def(s1)), Symb(Def(s2))) -> s1 == s2
    | (Prod(_,a1,b1), Prod(_,a2,b2)) -> eq a1 a2 && eq_binder b1 b2
    | (Abst(_,a1,t1), Abst(_,a2,t2)) -> eq a1 a2 && eq_binder t1 t2
    | (Appl(_,t1,u1), Appl(_,t2,u2)) -> eq t1 t2 && eq u1 u2
    | (Wild         , _            ) -> assert false
    | (_            , Wild         ) -> assert false
    | (ITag(_)      , _            ) -> assert false
    | (_            , ITag(_)      ) -> assert false
    | (Unif(u1,e1)  , Unif(u2,e2)  ) -> u1 == u2 && Array.for_all2 eq e1 e2
    | (_            , _            ) -> false
  in eq a b

(** Representation of a stack for the abstract machine used for evaluation. *)
type stack = term ref list

(* NOTE the stack contain references so that the computation of arguments when
   matching reduction rules may be shared. *)

(** [to_term t stk] builds a term from an abstract machine state [(t,stk)]. *)
let to_term : term -> stack -> term = fun t args ->
  let rec to_term t args =
    match args with
    | []      -> t
    | u::args -> to_term (appl t !u) args
  in to_term t args

(** [whnf t] computes a weak head normal form of the term [t]. *)
let rec whnf : term -> term = fun t ->
  if !debug_eval then log "eval" "evaluating %a" pp t;
  let (u, stk) = whnf_stk t [] in
  let u = to_term u stk in
  if !debug_eval then log "eval" "produced %a" pp u; u

(** [whnf_stk t stk] computes the weak head normal form of  [t] applied to the
    argument list (or stack) [stk]. Note that the normalisation is done in the
    sense of [whnf]. *)
and whnf_stk : term -> stack -> term * stack = fun t stk ->
  match (unfold t, stk) with
  (* Push argument to the stack. *)
  | (Appl(_,f,u) , stk    )       -> whnf_stk f (ref u :: stk)
  (* Beta reduction. *)
  | (Abst(_,_,f) , u::stk )       -> whnf_stk (Bindlib.subst f !u) stk
  (* Try to rewrite. *)
  | (Symb(Def(s)), stk    ) as st ->
      begin
        match find_rule s stk with
        | None        -> st
        | Some(t,stk) -> whnf_stk t stk
      end
  (* In head normal form. *)
  | (_           , _      ) as st -> st

(** [find_rule s stk] attempts to find a reduction rule of [s], that may apply
    under the stack [stk]. If such a rule is found, the machine state produced
    by its application is returned. *)
and find_rule : def -> stack -> (term * stack) option = fun s stk ->
  let stk_len = List.length stk in
  let match_rule r =
    (* First check that we have enough arguments. *)
    if r.arity > stk_len then None else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let env = Array.init (Bindlib.mbinder_arity r.lhs) (fun i -> ITag(i)) in
    let lhs = Bindlib.msubst r.lhs env in
    if !debug_eval then log "eval" "RULE trying rule [%a]" pp_rule (s,r);
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args ps ts =
      match (ps, ts) with
      | ([]   , _    ) -> Some(Bindlib.msubst r.rhs env, ts)
      | (p::ps, t::ts) -> if matching env p t then match_args ps ts else None
      | (_    , _    ) -> assert false (* cannot happen *)
    in
    match_args lhs stk
  in
  List.map_find match_rule s.def_rules

(** [matching ar p t] checks that term [t] matches pattern [p]. The values for
    pattern variables (using the [ITag] node) are stored in [ar], at the index
    they denote. In case several different values are found for a same pattern
    variable, equality modulo is computed to check compatibility. *)
and matching : term array -> term -> term ref -> bool = fun ar p t ->
  if !debug_eval then log "matc" "[%a] =~= [%a]" pp p pp !t;
  let res =
    (* First handle patterns that do not need the evaluated term. *)
    match p with
    | ITag(i) when ar.(i) = ITag(i) -> ar.(i) <- !t; true
    | Wild                          -> true
    | _                             ->
    (* Other cases need the term to be evaluated. *)
    t := whnf !t;
    match (p, !t) with
    | (ITag(i)      , t            ) -> eq_modulo ar.(i) t (* t <> ITag(i) *)
    | (Abst(_,_,t1) , Abst(_,_,t2) ) ->
        let (_,t1,t2) = Bindlib.unbind2 mkfree t1 t2 in
        matching ar t1 (ref t2)
    | (Appl(_,t1,u1), Appl(_,t2,u2)) ->
        matching ar t1 (ref t2) && matching ar u1 (ref u2)
    | (Vari(x1)     , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Symb(s1)     , Symb(s2)     ) -> s1 == s2
    | (_            , _            ) -> false
  in
  if !debug_eval then log "matc" (r_or_g res "[%a] =~= [%a]") pp p pp !t; res

(** [eq_modulo a b] tests equality modulo rewriting between [a] and [b]. *)
and eq_modulo : term -> term -> bool = fun a b ->
  if !debug_equa then log "equa" "%a == %a" pp a pp b;
  let rec eq_modulo l =
    match l with
    | []                   -> true
    | (a,b)::l when eq a b -> eq_modulo l
    | (a,b)::l             ->
        let (a,sa) = whnf_stk a [] in
        let (b,sb) = whnf_stk b [] in
        let rec sync acc la lb =
          match (la, lb) with
          | ([]   , []   ) -> (a, b, acc)
          | (a::la, b::lb) -> sync ((!a,!b)::acc) la lb
          | (la   , []   ) -> (to_term a (List.rev la), b, acc)
          | ([]   , lb   ) -> (a, to_term b (List.rev lb), acc)
        in
        let (a,b,l) = sync l (List.rev sa) (List.rev sb) in
        match (a, b) with
        | (a            , b            ) when eq a b -> eq_modulo l
        | (Abst(_,aa,ba), Abst(_,ab,bb)) ->
            let (_,ba,bb) = Bindlib.unbind2 mkfree ba bb in
            eq_modulo ((aa,ab)::(ba,bb)::l)
        | (Prod(_,aa,ba), Prod(_,ab,bb)) ->
            let (_,ba,bb) = Bindlib.unbind2 mkfree ba bb in
            eq_modulo ((aa,ab)::(ba,bb)::l)
        | (a            , b            ) -> false
  in
  let res = eq_modulo [(a,b)] in
  if !debug_equa then log "equa" (r_or_g res "%a == %a") pp a pp b; res

(** [snf t] computes the strong normal form of the term [t]. *)
let rec snf : term -> term = fun t ->
  let h = whnf t in
  match h with
  | Vari(_)     -> h
  | Type        -> h
  | Kind        -> h
  | Symb(_)     -> h
  | Prod(i,a,b) ->
      let (x,b) = Bindlib.unbind mkfree b in
      let b = snf b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Prod(i, snf a, b)
  | Abst(i,a,b) ->
      let (x,b) = Bindlib.unbind mkfree b in
      let b = snf b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Abst(i, snf a, b)
  | Appl(i,t,u) -> Appl(i, snf t, snf u)
  | Unif(_,_)   -> assert false
  | ITag(_)     -> assert false
  | Wild        -> assert false

(** [hnf t] computes the head normal form of the term [t]. *)
let rec hnf : term -> term = fun t ->
  match whnf t with
  | Appl(i,t,u) -> Appl(i, hnf t, hnf u)
  | t           -> t

(** Type representing the different evaluation strategies. *)
type strategy = WHNF | HNF | SNF

(** Configuration for evaluation. *)
type config =
  { strategy : strategy   (** Evaluation strategy.          *)
  ; steps    : int option (** Max number of steps if given. *) }

(** [eval cfg t] evaluates the term [t] according to configuration [cfg]. *)
let eval : config -> term -> term = fun c t ->
  match (c.strategy, c.steps) with
  | (_   , Some(0)) -> t
  | (WHNF, None   ) -> whnf t
  | (SNF , None   ) -> snf t
  | (HNF , None   ) -> hnf t
  (* TODO implement the rest. *)
  | (WHNF, Some(m)) -> wrn "number of steps not supported for WHNF...\n"; t
  | (HNF , Some(m)) -> wrn "number of steps not supported for HNF...\n"; t
  | (SNF , Some(m)) -> wrn "number of steps not supported for SNF...\n";  t
