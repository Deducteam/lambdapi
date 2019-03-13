(** Evaluation and conversion. *)

open Extra
open Timed
open Console
open Terms
open Basics
open Print

(** [with_trees] contains whether trees are used for pattern matching. *)
let with_trees : bool Pervasives.ref = Pervasives.ref false

(** Logging function for evaluation. *)
let log_eval = new_logger 'r' "eval" "debugging information for evaluation"
let log_eval = log_eval.logger

(** Logging function for equality modulo rewriting. *)
let log_eqmd = new_logger 'e' "eqmd" "debugging information for equality"
let log_eqmd = log_eqmd.logger

(** Representation of a single stack element (see {!type:stack}). Note that we
    use a references to allow a form of lazy evaluation when matching patterns
    (see {!val:matching}). The boolean tells whether a particular argument has
    already been normalized (to weak head normal form).  Note that an argument
    (i.e., an element of the stack) does not need to be evaluated when machted
    against a wildcard or a pattern variable. *)
type stack_elt = (bool * term) Pervasives.ref

(** Representation of a stack for the abstract machine used for evaluation. *)
type stack = stack_elt list

(** [to_term t stk] builds a term from an abstract machine state [(t,stk)]. *)
let to_term : term -> stack -> term = fun t args ->
  let rec to_term t args =
    match args with
    | []      -> t
    | u::args -> to_term (Appl(t,snd Pervasives.(!u))) args
  in to_term t args

(** [extract x p] extracts the term at position [p] from list of terms [x]. *)
let extract : term list -> Position.t -> term = fun xs p ->
  let rec loop xs p acc = match p with
    | [] -> acc
    | hdp :: tlp ->
       let elt = List.nth xs hdp in
       begin
         match elt with
         | Appl(_, _) as a -> let f, args = Basics.get_args a in
                             loop args tlp f
         | Abst(_, _)      -> assert false
         | Symb(_, _)
         | Patt(_, _, _)   -> assert false
         | _               -> assert false
       end in
  loop xs p (Patt(None, "", [| |]))

(** Evaluation step counter. *)
let steps : int Pervasives.ref = Pervasives.ref 0

(** [whnf t] computes a weak head normal form of the term [t]. *)
let rec whnf : term -> term = fun t ->
  if !log_enabled then log_eval "evaluating [%a]" pp t;
  let s = Pervasives.(!steps) in
  let t = unfold t in
  let (u, stk) = whnf_stk t [] in
  if Pervasives.(!steps) <> s then to_term u stk else t

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
  | (Symb(s,_), stk    ) ->
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
  if Pervasives.(!with_trees) then tree_walk !(s.sym_tree) stk else
  let stk_len = List.length stk in
  let match_rule r =
    (* First check that we have enough arguments. *)
    if r.arity > stk_len then None else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let env = Array.make (Bindlib.mbinder_arity r.rhs) TE_None in
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args ps ts =
      match (ps, ts) with
      | ([]   , _    ) -> Some(Bindlib.msubst r.rhs env, ts)
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
  if !log_enabled then
    log_eval "[%a] =~= [%a]" pp p pp (snd (Pervasives.(!t)));
  let res =
    (* First handle patterns that do not need the evaluated term. *)
    match p with
    | Patt(Some(i),_,[||]) when ar.(i) = TE_None ->
        let fn _ = snd Pervasives.(!t) in
        let b = Bindlib.raw_mbinder [||] [||] 0 mkfree fn in
        ar.(i) <- TE_Some(b); true
    | Patt(Some(i),_,e   ) when ar.(i) = TE_None ->
        let b = Bindlib.bind_mvar (to_tvars e) (lift (snd Pervasives.(!t))) in
        ar.(i) <- TE_Some(Bindlib.unbox b); Bindlib.is_closed b
    | Patt(None   ,_,[||]) -> true
    | Patt(None   ,_,e   ) ->
        let b = Bindlib.bind_mvar (to_tvars e) (lift (snd Pervasives.(!t))) in
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
    | (Symb(s1,_)       , Symb(s2,_)   ) -> s1 == s2
    | (_                , _            ) -> false
  in
  if !log_enabled then
    log_eval (r_or_g res "[%a] =~= [%a]") pp p pp (snd Pervasives.(!t));
  res

(** [eq_modulo a b] tests equality modulo rewriting between [a] and [b]. *)
and eq_modulo : term -> term -> bool = fun a b ->
  if !log_enabled then log_eqmd "[%a] == [%a]" pp a pp b;
  let rec eq_modulo l =
    match l with
    | []       -> ()
    | (a,b)::l ->
    let a = unfold a and b = unfold b in
    if a == b then eq_modulo l else
    match (whnf a, whnf b) with
    | (Patt(_,_,_), _          )
    | (_          , Patt(_,_,_))
    | (TEnv(_,_)  , _          )
    | (_          , TEnv(_,_)  )
    | (Kind       , _          )
    | (_          , Kind       ) -> assert false
    | (Type       , Type       ) -> eq_modulo l
    | (Vari(x1)   , Vari(x2)   ) when Bindlib.eq_vars x1 x2 -> eq_modulo l
    | (Symb(s1,_) , Symb(s2,_) ) when s1 == s2 -> eq_modulo l
    | (Prod(a1,b1), Prod(a2,b2))
    | (Abst(a1,b1), Abst(a2,b2)) ->
        let (_,b1,b2) = Bindlib.unbind2 b1 b2 in
        eq_modulo ((a1,a2)::(b1,b2)::l)
    | (Appl(t1,u1), Appl(t2,u2)) -> eq_modulo ((u1,u2)::(t1,t2)::l)
    | (Meta(m1,a1), Meta(m2,a2)) when m1 == m2 ->
        eq_modulo (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | (_          , _          ) -> raise Exit
  in
  let res = try eq_modulo [(a,b)]; true with Exit -> false in
  if !log_enabled then log_eqmd (r_or_g res "%a == %a") pp a pp b; res

(** [tree_walk t s] tries to match stack [s] against tree [t] *)
and tree_walk : Dtree.t -> stack -> (term * stack) option = fun itree istk ->
  (* Count maximum number of stored items to initialize variable array *)
  let capacity = Dtree.iter (fun _ _ -> 0)
    (fun _ store subr defr ->
      let maxch = if subr = [] then 0
        else List.extremum (>) (snd (List.split subr)) in
      let maxchd = match defr with
        | None     -> maxch
        | Some(dr) -> max dr maxch in
    if store then succ maxchd else maxchd) 0 itree in
  let vars = Array.init capacity (fun _ -> Patt(None, "", [| |])) in

  (* [walk t s c] where [s] is the stack of terms to match and [c] the cursor
     indicating where to write in the [env] array . *)
  let rec walk : Dtree.t -> stack -> int -> (term * stack) option =
    fun tree stk cursor ->
      match tree with
      | Fail                                  -> None
      | Leaf(env_builder, act)                ->
         assert (IntMap.cardinal env_builder = Bindlib.mbinder_arity act) ;
        let pre_env = IntMap.fold (fun pos sl pe ->
          IntMap.add sl vars.(pos) pe) env_builder IntMap.empty in
         (* Create the environment *)
         let env = Array.init (IntMap.cardinal pre_env) (fun _ -> TE_None) in
         IntMap.iter (fun sl te ->
           let inject _ = te in
           let b = Bindlib.raw_mbinder [| |] [| |] 0 mkfree inject in
           env.(sl) <- TE_Some(b)) pre_env ;
         Some(Bindlib.msubst act env, stk)
      | Node({ swap ; children ; store ; default }) ->
        if stk = [] then (* None *) assert false else (* If stack too short *)
        (* The main operations are: (i) picking the right term in the terms
           stack, (ii) filling the stack containing terms to be substituted
           in {!recfield:rhs} (or {!type:action}), (iii) branching on the
           correct branch. *)
        (* (i) *)
        let stk = match swap with
          | None    -> stk
          | Some(i) -> List.bring i stk in
        let examined = List.hd stk in
        if not (fst Pervasives.(!examined))
        then Pervasives.(examined := (true, whnf (snd !examined))) ;
        (* ^ This operation ought to be removed since with trees, each element
           of the stack is inspected only once. *)
        let hd, tlstk = match snd Pervasives.(!examined) with
          | Appl(_, _) as a ->
             let t, la = Basics.get_args a in
             let unfolded = List.map (fun e -> Pervasives.ref (false, e)) la in
             t, unfolded @ (List.tl stk)
          | Symb(_, _) as s ->
             s, List.tl stk
          | Abst(_, _)      -> assert false
          | _               -> assert false in
        (* (ii) *)
        if store then vars.(cursor) <- hd ;
        let ncurs = if store then succ cursor else cursor in
        (* (iii) *)
        let matched_on_cons = List.assoc_opt hd children in
        let matched = match matched_on_cons with
          | Some(_) as s -> s
          | None         -> default in
        Option.bind (fun tr -> walk tr tlstk ncurs) matched in
  walk itree istk 0

(** {b Note} During the matching with trees, two term stacks are used.
    - One is of type {!type:stack} and contains the arguments of a symbol that
      are being matched against the rules of the symbol in order to rewrite
      those arguments.
    - The other is created during the matching, of type {!type:term Stack.t}
      and contains the terms which, in the previous stack, have been matched
      against a pattern variables in some rule.  The terms in this stack might
      be substituted in the right hand side of the rule. *)

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
  | Wild        -> assert false
  | TRef(_)     -> assert false

(** [hnf t] computes the head normal form of the term [t]. *)
let rec hnf : term -> term = fun t ->
  match whnf t with
  | Appl(t,u) -> Appl(hnf t, hnf u)
  | t         -> t

(** Type representing the different evaluation strategies. *)
type strategy = WHNF | HNF | SNF | NONE

(** Configuration for evaluation. *)
type config =
  { strategy : strategy   (** Evaluation strategy.          *)
  ; steps    : int option (** Max number of steps if given. *) }

(** [eval cfg t] evaluates the term [t] according to configuration [cfg]. *)
let eval : config -> term -> term = fun c t ->
  match (c.strategy, c.steps) with
  | (_   , Some(0))
  | (NONE, _      ) -> t
  | (WHNF, None   ) -> whnf t
  | (SNF , None   ) -> snf t
  | (HNF , None   ) -> hnf t
  (* TODO implement the rest. *)
  | (_   , Some(_)) -> wrn None "Number of steps not supported."; t
