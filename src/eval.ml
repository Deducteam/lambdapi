(** Evaluation and conversion. *)

open Extra
open Timed
open Console
open Terms
open Print

(** Representation of a stack for the abstract machine used for evaluation. *)
type stack = (bool * term) Pervasives.ref list

(** Representation of a single stack element. *)
type stack_elt = (bool * term) Pervasives.ref

(* NOTE the stack contain references so that the computation of arguments when
   matching reduction rules may be shared. *)

(** [to_term t stk] builds a term from an abstract machine state [(t,stk)]. *)
let to_term : term -> stack -> term = fun t args ->
  let rec to_term t args =
    match args with
    | []      -> t
    | u::args -> to_term (Appl(t,snd Pervasives.(!u))) args
  in to_term t args

(** Evaluation step counter. *)
let steps : int Pervasives.ref = Pervasives.ref 0

(** [whnf t] computes a weak head normal form of the term [t]. *)
let rec whnf : term -> term = fun t ->
  if !debug_eval then log "eval" "evaluating [%a]" pp (unfold t);
  let (u, stk) = whnf_stk t [] in
  to_term u stk

(** [whnf_stk t stk] computes the weak head normal form of  [t] applied to the
    argument list (or stack) [stk]. Note that the normalisation is done in the
    sense of [whnf]. *)
and whnf_stk : term -> stack -> term * stack = fun t stk ->
  let st = (unfold t, stk) in
  match st with
  (* Push argument to the stack. *)
  | (Appl(f,u), stk    ) ->
      whnf_stk f (Pervasives.ref (false, u) :: stk)
  (* Beta reduction. *)
  | (Abst(_,f), u::stk ) ->
      Pervasives.incr steps;
      whnf_stk (Bindlib.subst f (snd Pervasives.(!u))) stk
  (* Try to rewrite. *)
  | (Symb(s)  , stk    ) ->
      begin
        match Timed.(!(s.sym_def)) with
        | Some(t) -> Pervasives.incr steps; whnf_stk t stk
        | None    ->
        match find_rule s stk with
        | None        -> st
        | Some(t,stk) -> Pervasives.incr steps; whnf_stk t stk
      end
  (* In head normal form. *)
  | (_        , _      ) -> st

(** [find_rule s stk] attempts to find a reduction rule of [s], that may apply
    under the stack [stk]. If such a rule is found, the machine state produced
    by its application is returned. *)
and find_rule : sym -> stack -> (term * stack) option = fun s stk ->
  let stk_len = List.length stk in
  let match_rule r =
    (* First check that we have enough arguments. *)
    if r.arity > stk_len then None else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let env = Array.make (Bindlib.mbinder_arity r.rhs) TE_None in
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args ps ts =
      match (ps, ts) with
      | ([]   , _    ) ->
         begin
           if !debug_eval then log "eval" "%a" pp_rule (s,r);
           Some(Bindlib.msubst r.rhs env, ts)
         end
      | (p::ps, t::ts) -> if matching env p t then match_args ps ts else None
      | (_    , _    ) -> assert false (* cannot happen *)
    in
    match_args r.lhs stk
  in
  List.map_find match_rule Timed.(!(s.sym_rules))

(** [matching ar p t] checks that term [t] matches pattern [p]. The values for
    pattern variables (using the [ITag] node) are stored in [ar], at the index
    they denote. In case several different values are found for a same pattern
    variable, equality modulo is computed to check compatibility. *)
and matching : term_env array -> term -> stack_elt -> bool = fun ar p t ->
  if !debug_matc then
    log "matc" "[%a] =~= [%a]" pp p pp (snd (Pervasives.(!t)));
  let res =
    (* First handle patterns that do not need the evaluated term. *)
    match p with
    | Patt(Some(i),_,[||]) when ar.(i) = TE_None ->
        let fn _ = snd Pervasives.(!t) in
        let b = Bindlib.raw_mbinder [||] [||] 0 mkfree fn in
        ar.(i) <- TE_Some(b); true
    | Patt(Some(i),_,e   ) when ar.(i) = TE_None ->
        let fn t = match t with Vari(x) -> x | _ -> assert false in
        let vars = Array.map fn e in
        let b = Bindlib.bind_mvar vars (lift (snd Pervasives.(!t))) in
        ar.(i) <- TE_Some(Bindlib.unbox b); Bindlib.is_closed b
    | Patt(None,_,[||]) -> true
    | Patt(None,_,e   ) ->
        let fn t = match t with Vari(x) -> x | _ -> assert false in
        let vars = Array.map fn e in
        let b = Bindlib.bind_mvar vars (lift (snd Pervasives.(!t))) in
        Bindlib.is_closed b
    | _                                 ->
    (* Other cases need the term to be evaluated. *)
    if not (fst Pervasives.(!t)) then Pervasives.(t := (true, whnf (snd !t)));
    match (p, snd Pervasives.(!t)) with
    | (Patt(Some(i),_,e), t            ) -> (* ar.(i) <> TE_None *)
        let b = match ar.(i) with TE_Some(b) -> b | _ -> assert false in
        eq_modulo (Bindlib.msubst b e) t
    | (Abst(_,t1)       , Abst(_,t2)   ) ->
        let (_,t1,t2) = Bindlib.unbind2 t1 t2 in
        matching ar t1 (Pervasives.ref (false, t2))
    | (Appl(t1,u1)      , Appl(t2,u2)  ) ->
        matching ar t1 (Pervasives.ref (fst Pervasives.(!t), t2))
        && matching ar u1 (Pervasives.ref (false, u2))
    | (Vari(x1)         , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Symb(s1)         , Symb(s2)     ) -> s1 == s2
    | (_                , _            ) -> false
  in
  if !debug_matc then
    log "matc" (r_or_g res "[%a] =~= [%a]") pp p pp (snd Pervasives.(!t));
  res

(** [eq_modulo a b] tests equality modulo rewriting between [a] and [b]. *)
and eq_modulo : term -> term -> bool = fun a b ->
  if !debug_equa then log "eq_modulo" "[%a] [%a]" pp a pp b;
  let rec eq_modulo l =
    match l with
    | []       -> ()
    | (a,b)::l ->
    match (whnf a, whnf b) with
    | (Patt(_,_,_), _          )
    | (_          , Patt(_,_,_))
    | (TEnv(_,_)  , _          )
    | (_          , TEnv(_,_)  )
    | (Kind       , _          )
    | (_          , Kind       ) -> assert false
    | (Type       , Type       ) -> eq_modulo l
    | (Vari(x1)   , Vari(x2)   ) when Bindlib.eq_vars x1 x2 -> eq_modulo l
    | (Symb(s1)   , Symb(s2)   ) when s1 == s2 -> eq_modulo l
    | (Prod(a1,b1), Prod(a2,b2))
    | (Abst(a1,b1), Abst(a2,b2)) -> eq_modulo ((a1,a2)::(unbind2 b1 b2)::l)
    | (Appl(t1,u1), Appl(t2,u2)) -> eq_modulo ((u1,u2)::(t1,t2)::l)
    | (Meta(m1,a1), Meta(m2,a2)) when m1 == m2 ->
        eq_modulo (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | (_          , _          ) -> raise Exit
  in
  let res = try eq_modulo [(a,b)]; true with Exit -> false in
  if !debug_equa then log "equa" (r_or_g res "%a == %a") pp a pp b; res

let whnf : term -> term = fun t ->
  let t = unfold t in
  Pervasives.(steps := 0);
  let u = whnf t in
  if Pervasives.(!steps = 0) then t else u

(** [snf t] computes the strong normal form of the term [t]. *)
let rec snf : term -> term = fun t ->
  let h = whnf t in
  match h with
  | Vari(_)     -> h
  | Type        -> h
  | Kind        -> h
  | Symb(_)     -> h
  | Prod(a,b)   ->
      let (x,b) = Bindlib.unbind b in
      let b = snf b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Prod(snf a, b)
  | Abst(a,b)   ->
      let (x,b) = Bindlib.unbind b in
      let b = snf b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Abst(snf a, b)
  | Appl(t,u)   -> Appl(snf t, snf u)
  | Meta(m,ts)  -> Meta(m, Array.map snf ts)
  | Patt(_,_,_) -> assert false
  | TEnv(_,_)   -> assert false

(** [hnf t] computes the head normal form of the term [t]. *)
let rec hnf : term -> term = fun t ->
  match whnf t with
  | Appl(t,u) -> Appl(hnf t, hnf u)
  | t         -> t

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
  | (WHNF, Some(_)) -> wrn "number of steps not supported for WHNF...\n"; t
  | (HNF , Some(_)) -> wrn "number of steps not supported for HNF...\n"; t
  | (SNF , Some(_)) -> wrn "number of steps not supported for SNF...\n";  t
