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

(* Suffix [_t] for "tree" version *)

(** [to_term_t t k] builds a term from a symbol and its arguments. *)
let to_term_t : term -> term list -> term = fun t args ->
  let rec to_term_t t = function
    | [] -> t
    | u :: args -> to_term_t (Appl(t, u)) args in
  to_term_t t args

(** Evaluation step counter. *)
let steps : int Pervasives.ref = Pervasives.ref 0

(** [whnf t] computes a weak head normal form of the term [t]. *)
let rec whnf : term -> term = fun t ->
  if !log_enabled then log_eval "evaluating [%a]" pp t;
  let s = Pervasives.(!steps) in
  let t = unfold t in
  if Pervasives.(!with_trees) then whnf_stk_t t [] else
  let u, stk = whnf_stk t [] in
  if Pervasives.(!steps) <> s then to_term u stk else t

(** [whnf_stk_t t k] computes the weak head normal form of [t] applied to
    arguments [k].  Note that the normalisation is done in thee sense of
    [whnf]. *)
and whnf_stk_t : term -> term list -> term = fun t stk ->
  match (unfold t, stk) with
  (* Push argument to the stack. *)
  | Appl(_, _), _ as st   ->
     let f, args = Basics.get_args (fst st) in
     whnf_stk_t f (args @ stk)
  (* Beta reduction. *)
  | Abst(_, f), u :: stk  ->
     whnf_stk_t (Bindlib.subst f u) stk
  (* Try to rewrite. *)
  | Symb(s, _), stk as st ->
     begin match Timed.(!(s.sym_def)) with
     | Some(t) -> whnf_stk_t t stk
     | None    ->
     match find_rule_t s stk with
     (* If no rule is found, build back the Appl *)
     | None    -> to_term_t (fst st) stk
     | Some(t) -> whnf t
     end
  (* In head normal form. *)
  | _         , _         -> t

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

(** [find_rule_t s k] attempts to find a reduction rule of [s] when applied to
    arguments [k].  Returns the reduced term if a rule if found, [None]
    otherwise. *)
and find_rule_t : sym -> term list -> term option = fun s stk ->
  let de, tr = !(s.sym_tree) in
  let de, tr = Lazy.force de, Lazy.force tr in
  tree_walk tr de (Array.of_list stk)

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

(** [tree_walk t d s] tries to match stack [s] against tree [t] of depth [d]. *)
and tree_walk : Dtree.t -> int -> term array -> term option =
  fun itree capa istk ->
  let vars = Array.make capa (Patt(None, "", [| |])) in
  (* [walk t s c] where [s] is the stack of terms to match and [c] the cursor
     indicating where to write in the [env] array described in {!module:Terms}
     as the environment of the RHS during matching. *)
  let rec walk : Dtree.t -> term array -> int -> term option =
    fun tree stk cursor ->
    (* XXX stack could be modified in place and not taken as arg *)
      match tree with
      | Fail                                  -> None
      | Leaf(env_builder, act)                ->
         (* Retrieve terms needed in the action from the [vars] array *)
         (* [pre_env] is the same as [env] but without binders *)
         let pre_env = IntMap.fold (fun pos env_slot acc ->
           IntMap.add env_slot vars.(pos) acc) env_builder IntMap.empty in
         let env = Array.make (IntMap.cardinal pre_env) TE_None in
         IntMap.iter (fun slot te ->
           let inject _ = te in
           let b = Bindlib.raw_mbinder [| |] [| |] 0 mkfree inject in
           env.(slot) <- TE_Some(b)) pre_env ;
         Some(Bindlib.msubst act env)
      | Node({ swap ; children ; store ; default ; _ }) ->
         let si = Option.get swap 0 in
         (* Quit if stack is too short*)
         if stk = [| |] || si >= Array.length stk then None else 
         (* Pick the right term in the stack *)
         let examined = whnf stk.(si) in
         (* Store hd of stack if needed *)
         if store then
           begin if !log_enabled then log_eval "storing [%a]" pp examined ;
                 vars.(cursor) <- examined
           end ;
         let cursor = if store then succ cursor else cursor in
         (* Fetch the right subtree and the new stack *)
         (* [choose t s] chooses a tree among {!val:children} when term [t] is
            examined and returns the new head of stack. *)
         let rec choose te stk_part : tree option * term list =
           match te with
           | Appl(_, _) ->
              let hs, args = Basics.get_args te in
              choose hs (args @ stk_part)
           | Symb({ sym_name ; _ }, _) ->
              let nargs = List.length stk_part in
              let consname = Dtree.add_args_repr sym_name nargs in
              let matched_on_cons = StrMap.find_opt consname children in
              let matched = match matched_on_cons with
                | Some(_) ->
                   if !log_enabled then
                    log_eval (r_or_g true "[%s] =~= [%a]") consname pp
                      examined ;
                  matched_on_cons
                | None    -> default in
              matched, stk_part
           | Abst(_, _) -> assert false
           | Meta(_, _) -> assert false
           | _          -> assert false in
         let matched, stk_part = choose examined [] in
         let stk =
           let postfix = if si >= Array.length stk then [| |] else
                           Array.sub stk (si + 1)
                             (Array.length stk - (si + 1)) in
           Array.concat [ Array.sub stk 0 si
                        ; Array.of_list stk_part
                        ; postfix ] in
         Option.bind (fun tr -> walk tr stk cursor) matched in
  walk itree istk 0

(** {b Note} During the matching with trees, two structures containing terms
    are used.
    - The first of type {!type:stack} contains the arguments of a symbol that
      are being matched against the rules of the symbol in order to rewrite
      those arguments to a right hand side.
    - The other of type {!type:term array} is filled during the matching and
      contains the terms from the input stack that have been matched against a
      pattern variable {!constructor:Patt} in some lhs.  The terms in this
      stack might be substituted in the right hand side of the rule. *)

let whnf : term -> term = fun t ->
  let t = unfold t in
  Pervasives.(steps := 0);
  let u = whnf t in
  if Pervasives.(!with_trees) then u else
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
