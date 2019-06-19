(** Evaluation and conversion. *)

open Extra
open Timed
open Console
open Terms
open Basics
open Print
module TC = Treecons

(** The head-structure of a term t is:
- λx:_,h if t=λx:a,u and h is the head-structure of u
- ∀ if t=∀x:a,u
- h _ if t=uv and h is the head-structure of u
- ? if t=?M[t1,..,tn] (and ?M is not instanciated)
- t itself otherwise (TYPE, KIND, x, f)

A term t is in head-normal form (hnf) if its head-structure is invariant by
reduction.

A term t is in weak head-normal form (whnf) if it is an abstration or if it
is in hnf. In particular, a term in head-normal form is in weak head-normal
form.

A term t is in strong normal form (snf) if it cannot be reduced further.
*)

(** Used to distinguish free variables across evaluations, avoid re intrance
    issues. *)
let stamp = Pervasives.ref 0

(** Used to indicate a default case. *)
exception Default

(** Logging function for evaluation. *)
let log_eval = new_logger 'r' "eval" "debugging information for evaluation"
let log_eval = log_eval.logger

(** [le_fvc s x] is a logging function used when verifying a closeness
    constraint. *)
let le_fvc : bool -> tvar array -> unit = fun b xs ->
  log_eval (r_or_g b "free var check on [%a]")
    (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_tvar)
    (Array.to_list xs)

(** Logging function for equality modulo rewriting. *)
let log_eqmd = new_logger 'e' "eqmd" "debugging information for equality"
let log_eqmd = log_eqmd.logger

(** Evaluation step counter.  Allow to conserve physical equality in
    {!val:whnf}. *)
let steps : int Pervasives.ref = Pervasives.ref 0

(** [whnf_beta t] computes a weak head beta normal form of the term [t]. *)
let rec whnf_beta : term -> term = fun t ->
  if !log_enabled then log_eval "evaluating [%a]" pp t;
  let s = Pervasives.(!steps) in
  let t = unfold t in
  let (u, stk) = whnf_beta_stk t [] in
  if Pervasives.(!steps) <> s then add_args u stk else t

(** [whnf_beta_stk t stk] computes the weak head beta normal form of [t]
   applied to the argument list (or stack) [stk]. Note that the normalisation
   is done in the sense of [whnf]. *)
and whnf_beta_stk : term -> term list -> term * term list = fun t stk ->
  let st = (unfold t, stk) in
  match st with
  (* Push argument to the stack. *)
  | (Appl(f,u), stk    ) ->
      whnf_beta_stk f (u :: stk)
  (* Beta reduction. *)
  | (Abst(_,f), u::stk ) ->
      Pervasives.incr steps;
      whnf_beta_stk (Bindlib.subst f u) stk
  (* In head beta normal form. *)
  | (_        , _      ) -> st

(** [whnf_beta t] computes a weak head beta normal form of [t]. *)
let whnf_beta : term -> term = fun t ->
  Pervasives.(steps := 0);
  let t = unfold t in
  let u = whnf_beta t in
  if Pervasives.(!steps = 0) then t else u

(** [whnf t] computes a weak head normal form of the term [t]. *)
let rec whnf : term -> term = fun t ->
  if !log_enabled then log_eval "evaluating [%a]" pp t;
  let s = Pervasives.(!steps) in
  let t = unfold t in
  let (u, stk) = whnf_stk t [] in
  if Pervasives.(!steps) <> s then add_args u stk else t

(** [whnf_stk t k] computes the weak head normal form of [t] applied to
    stack [k].  Note that the normalisation is done in the sense of [whnf]. *)
and whnf_stk : term -> term list -> term * term list = fun t stk ->
  let st = (unfold t, stk) in
  match st with
  (* Push argument to the stack. *)
  | (Appl(f,u), stk   ) ->
      whnf_stk f (sensible_tref u::stk)
  (* Beta reduction. *)
  | (Abst(_,f), u::stk) ->
      Pervasives.incr steps ;
      let t = Bindlib.subst f u in
      whnf_stk t stk
  (* Try to rewrite. *)
  | (Symb(s,_), stk   ) ->
      begin match !(s.sym_def) with
      | Some(t) -> Pervasives.incr steps ; whnf_stk t stk
      | None    ->
      match find_rule s stk with
      (* If no rule is found, return the original term *)
      | None        -> st
      | Some(t,stk) -> Pervasives.incr steps ; whnf_stk t stk
      end
  (* In head normal form. *)
  | (_         , _    ) -> st

(** [find_rule s k] attempts to find a reduction rule of [s] when applied to
    arguments [k].  Returns the reduced term if a rule if found, [None]
    otherwise. *)
and find_rule : sym -> term list -> (term * term list) option =
  fun s stk ->
  let capa, tr = !(s.sym_tree) in
  let capa, tr = Lazy.force capa, Lazy.force tr in
  tree_walk tr capa stk

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

(** [tree_walk t c s] tries to match stack [s] against tree [t] of capacity
    [c]. *)
and tree_walk : Dtree.t -> int -> term list -> (term * term list) option =
  fun tree capa stk ->
  let vars = Array.make capa Kind in (* dummy terms *)
  let boundv = Array.make capa None in
  let module R = Dtree.ReductionStack in
  let stk = R.of_list stk in
  (* [walk t s c m] where [s] is the stack of terms to match and [c] the
     cursor indicating where to write in the [env] array described in
     {!module:Terms} as the environment of the RHS during matching.  [m]
     maps the free variables contained in the tree to the free variables
     used in this evaluation. *)
  let rec walk tree stk cursor to_stamped =
    match tree with
    | Fail                                                -> None
    | Leaf(env_builder, act)                              ->
        (* Allocate an environment for the action. *)
        let env = Array.make (Bindlib.mbinder_arity act) TE_None in
        (* Retrieve terms needed in the action from the [vars] array. *)
        let fn (pos, slot) =
          match boundv.(pos) with
          | Some(b) ->
              env.(slot) <- TE_Some(b)
          | None    ->
              let t = unfold vars.(pos) in
              let b = Bindlib.raw_mbinder [||] [||] 0 mkfree (fun _ -> t) in
              env.(slot) <- TE_Some(b) in
        List.iter fn env_builder ;
        (* Actually perform the action. *)
        Some(Bindlib.msubst act env, R.to_list stk)
    | Condition({ ok ; condition ; fail }) ->
        let next = match condition with
          | TcstrEq(i, j)        ->
              if eq_modulo vars.(i) vars.(j) then ok else fail
          | TcstrFreeVars(xs, i) ->
              let b = lift vars.(i) in
              let xs = Array.map (fun e -> VarMap.find e to_stamped) xs in
              let bound = Bindlib.bind_mvar xs b in
              let r = Bindlib.is_closed bound in
              if !log_enabled then le_fvc r xs ;
              if r
              then ( boundv.(i) <- Some(Bindlib.unbox bound)
                   ; ok )
              else fail in
        walk next stk cursor to_stamped
    | Node({swap; children; store; abstraction; default}) ->
        try
          let left, examined, right = R.destruct stk swap in
          if TC.Map.is_empty children && abstraction = None then
            match default with
            | None    -> None
            | Some(t) ->
                let cursor = if store
                  then ( vars.(cursor) <- examined
                       ; cursor + 1 )
                  else cursor in
                walk t (R.restruct left [] right) cursor to_stamped else
          let s = Pervasives.(!steps) in
          let t, args = whnf_stk examined [] in
          let args = if store then List.map sensible_tref args else args in
          let rebuilt = lazy (add_args t args) in
          (* Introduce sharing on arguments *)
          begin if Pervasives.(!steps) <> s then match examined with
          (* If examined term was shared, and it has been reduced, update ref *)
          | TRef(v) -> v := Some(Lazy.force rebuilt)
          | _       -> () end ;
          let cursor = if store
            then ( vars.(cursor) <- Lazy.force rebuilt
                 ; cursor + 1 )
            else cursor in
          try begin match t with
            | Symb(s, _) ->
                let c_ari = List.length args in
                let cons = TC.Symb({ c_sym = s.sym_name ; c_mod = s.sym_path
                                   ; c_ari }) in
                let matched = TC.Map.find cons children in
                walk matched (R.restruct left args right) cursor to_stamped
            | Vari(x)    ->
                let cons = TC.Vari(Bindlib.name_of x) in
                let matched = TC.Map.find cons children in
                walk matched (R.restruct left args right) cursor to_stamped
            | Abst(_, b) ->
                begin match abstraction with
                | None         -> raise Default
                | Some(fv, tr) ->
                    let nfv = stamp_tvar Pervasives.(!stamp) fv in
                    Pervasives.incr stamp ;
                    let bound = Bindlib.subst b (mkfree nfv) in
                    let u = bound :: args in
                    let to_stamped = VarMap.add fv nfv to_stamped in
                    walk tr (R.restruct left u right) cursor to_stamped
                end
            | Meta(_, _) -> raise Default
            | _          -> assert false end
          with Not_found | Default ->
            begin match default with
            | None    -> None
            | Some(d) ->
                walk d (R.restruct left [] right) cursor to_stamped end
        with Not_found -> None in
  walk tree stk 0 VarMap.empty

(** {b Note} During the matching with trees, two structures containing terms
    are used.
    - The first of type {!type:term list} contains the arguments of a symbol
      that are being matched against its rules in order to rewrite those
      arguments to a right hand side.
    - The other, named {!val:vars} of type {!type:term array} is filled during
      the matching and contains the terms from the input stack that have been
      matched against a pattern variable {!constructor:Patt} in some lhs.
      A term might be in {!val:vars} either because it will be substituted in
      the rhs, and we thus have to save them; or the term is matched against a
      constrained {!constructor:Patt}, which may or may not be used in the
      rhs. See {!module:Terms}, {!type:term} for more information. *)

(** {b Note} When matching fails, even though {!val:tree_walk} returns
    {!constructor:None}, the input stack is updated (i.e. terms are possibly
    reduced) as sharing is used through {!constructor:TRef}.  Consequently,
    when a term is reduced in {!val:walk} with {!val:whnf_stk}, the term in
    the input stack is updated as well. *)

(** [whnf t] computes a weak head-normal form of [t]. *)
let whnf : term -> term = fun t ->
  Pervasives.(steps := 0);
  let t = unfold t in
  let u = whnf t in
  if Pervasives.(!steps = 0) then t else u

(** [simplify t] reduces simple redexes of [t]. *)
let rec simplify : term -> term = fun t ->
  match get_args (whnf_beta t) with
  | Prod(a,b), _ ->
     let x,b = Bindlib.unbind b in
     Prod (simplify a, Bindlib.unbox (Bindlib.bind_var x (lift (simplify b))))
  | h, ts -> add_args h (List.map whnf_beta ts)

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

(** [hnf t] computes a head-normal form of the term [t]. *)
let rec hnf : term -> term = fun t ->
  match whnf t with
  | Abst(a,t) ->
     let x,t = Bindlib.unbind t in
     Abst(a, Bindlib.unbox (Bindlib.bind_var x (lift (hnf t))))
  | t         -> t

(** Type representing the different evaluation strategies. *)
type strategy =
  | WHNF
  (** Reduce to weak head-normal form. *)
  | HNF
  (** Reduce to head-normal form. *)
  | SNF
  (** Reduce to strong normal form. *)
  | NONE
  (** Do nothing. *)

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
