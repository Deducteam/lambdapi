(** Evaluation and conversion. *)

open Extra
open Timed
open Console
open Terms
open Basics
open Print

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

(** Logging function for evaluation. *)
let log_eval = new_logger 'e' "eval" "evaluation"
let log_eval = log_eval.logger

(** Logging function for equality modulo rewriting. *)
let log_conv = new_logger 'c' "conv" "conversion"
let log_conv = log_conv.logger

(** Convert modulo eta. *)
let eta_equality : bool ref = Console.register_flag "eta_equality" false

(** Counter used to preserve physical equality in {!val:whnf}. *)
let steps : int Pervasives.ref = Pervasives.ref 0

(** Abstract machine stack. *)
type stack = term list

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
and whnf_beta_stk : term -> stack -> term * stack = fun t stk ->
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
and whnf_stk : term -> stack -> term * stack = fun t stk ->
  let st = (unfold t, stk) in
  match st with
  (* Push argument to the stack. *)
  | (Appl(f,u), stk   ) ->
      whnf_stk f (appl_to_tref u::stk)
  (* Beta reduction. *)
  | (Abst(_,f), u::stk) ->
      Pervasives.incr steps;
      whnf_stk (Bindlib.subst f u) stk
  (* Try to rewrite. *)
  | (Symb(s,_), stk   ) ->
      begin
      (* First check for symbol definition. *)
      match !(s.sym_def) with
      | Some(t) -> Pervasives.incr steps; whnf_stk t stk
      | None    ->
      (* Otherwise try rewriting using decision tree. *)
      match tree_walk !(s.sym_tree) stk with
      (* If no rule is found, return the original term *)
      | None        -> st
      | Some(t,stk) -> Pervasives.incr steps; whnf_stk t stk
      end
  (* In head normal form. *)
  | (_         , _    ) -> st

(** [eq_modulo a b] tests equality modulo rewriting between [a] and [b]. *)
and eq_modulo : term -> term -> bool = fun a b ->
  if !log_enabled then log_conv "[%a] == [%a]" pp a pp b;
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
    | (Abst(_ ,b ), t          )
    | (t          , Abst(_ ,b )) when !eta_equality ->
        let (x,b) = Bindlib.unbind b in
        eq_modulo ((b, Appl(t, Vari(x)))::l)
    | (Appl(t1,u1), Appl(t2,u2)) -> eq_modulo ((u1,u2)::(t1,t2)::l)
    | (Meta(m1,a1), Meta(m2,a2)) when m1 == m2 ->
        eq_modulo (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | (_          , _          ) -> raise Exit
  in
  let res = try eq_modulo [(a,b)]; true with Exit -> false in
  if !log_enabled then log_conv (r_or_g res "%a == %a") pp a pp b; res

(** {b NOTE} that matching with trees involves three collections of terms.
    1. The argument stack [stk] of type {!type:stack} which contains the terms
       that are matched against the decision tree.
    2. An array [vars] of variables that are used for non-linearity checks and
       free variable checks, or that are used in the RHS.
    3. A mapping [fresh_vars] from (free) variables to (free) variables, which
       is used to avoid reentrancy issues.

    The [bound] array is similar to the [vars] array except that it is used to
    save terms with free variables. *)

(** {b NOTE} bound variables involve three elements:
    1. a {!constructor:Terms.term.Abst} which introduces the bound variable in
       the term;
    2. a {!constructor:Terms.term.Vari} which is the bound variable previously
       introduced;
    3. a {!constructor:Tree_types.TC.t.Vari} which is a simplified
       representation of a variable for trees.

    Regarding reentrancy: each time an abstraction is matched, a fresh
    variable is created. If fresh variable [w] represents the variable [v]
    stored in the tree, the equality of the tree constructors for [v] and [w]
    must be ensured (for the correctness of the matching). *)

(** [tree_walk tree stk] tries to apply a rewriting rule by matching the stack
    [stk] agains the decision tree [tree]. The resulting state of the abstract
    machine is returned in case of success. Even if mathching fails, the stack
    [stk] may be imperatively updated: any reduction step taken in elements of
    the stack is preserved (this is done using {!constructor:TRef}). *)
and tree_walk : dtree -> stack -> (term * stack) option = fun tree stk ->
  let (lazy capacity, lazy tree) = tree in
  let vars = Array.make capacity Kind in (* dummy terms *)
  let bound = Array.make capacity TE_None in
  (* [walk t s c v i] where [s] is the stack of terms to match and [c] the
     cursor indicating where to write in the [vars] array described in
     {!module:Terms} as the environment of the RHS during matching. [v] maps
     the free variables contained in the term to the indexes defined during
     tree build, and [i] is the inverse mapping of [v]. *)
  let rec walk tree stk cursor vars_id id_vars =
    let open Tree_types in
    match tree with
    | Fail                                                -> None
    | Leaf(env_builder, act)                              ->
        (* Allocate an environment for the action. *)
        let env = Array.make (Bindlib.mbinder_arity act) TE_None in
        (* Retrieve terms needed in the action from the [vars] array. *)
        let fn (pos, (slot, xs)) =
          match bound.(pos) with
          | TE_Vari(_) -> assert false
          | TE_Some(_) -> env.(slot) <- bound.(pos)
          | TE_None    ->
              if Array.length xs = 0 then
                let t = unfold vars.(pos) in
                let b = Bindlib.raw_mbinder [||] [||] 0 mkfree (fun _ -> t) in
                env.(slot) <- TE_Some(b)
              else
                let b = lift vars.(pos) in
                let xs = Array.map (fun e -> IntMap.find e id_vars) xs in
                env.(slot) <- TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs b))
        in
        List.iter fn env_builder;
        (* Actually perform the action. *)
        Some(Bindlib.msubst act env, stk)
    | Cond({ ok ; cond ; fail })                          ->
        let next =
          match cond with
          | CondNL(i, j) ->
              if eq_modulo vars.(i) vars.(j) then ok else fail
          | CondFV(xs,i) ->
              let allowed = Array.map (fun e -> IntMap.find e id_vars) xs in
              (* FIXME some comparisons can be avoided. *)
              let fn b =
                let fn _ x = not (Bindlib.occur x b) in
                IntMap.for_all fn id_vars
              in
              (* We first attempt to match [vars.(i)] directly. *)
              let b = Bindlib.bind_mvar allowed (lift vars.(i)) in
              if fn b then (bound.(i) <- TE_Some(Bindlib.unbox b); ok) else
              (* As a last resort we try matching the SNF. *)
              let b = Bindlib.bind_mvar allowed (lift (snf vars.(i))) in
              if fn b then (bound.(i) <- TE_Some(Bindlib.unbox b); ok) else
              fail
        in
        walk next stk cursor vars_id id_vars
    | Eos(l, r)                                           ->
        let next = if stk = [] then l else r in
        walk next stk cursor vars_id id_vars
    | Node({swap; children; store; abstraction; default}) ->
        match List.destruct stk swap with
        | exception Not_found     -> None
        | (left, examined, right) ->
        if TCMap.is_empty children && abstraction = None then
          let fn t =
            let cursor =
              if store then (vars.(cursor) <- examined; cursor + 1)
              else cursor
            in
            let stk = List.reconstruct left [] right in
            walk t stk cursor vars_id id_vars
          in
          Option.map_default fn None default
        else
          let s = Pervasives.(!steps) in
          let (t, args) = whnf_stk examined [] in
          let args = if store then List.map appl_to_tref args else args in
          (* Introduce sharing on arguments *)
          if Pervasives.(!steps) <> s then
            begin
              match examined with
              | TRef(v) -> v := Some(add_args t args)
              | _       -> ()
            end;
          let cursor =
            if store then (vars.(cursor) <- add_args t args; cursor + 1)
            else cursor
          in
          let default () =
            let fn d =
              let stk = List.reconstruct left [] right in
              walk d stk cursor vars_id id_vars
            in
            Option.map_default fn None default
          in
          match t with
          | Symb(s, _) ->
              let cons = TC.Symb(List.length args, s.sym_name, s.sym_path) in
              begin
                try
                  let matched = TCMap.find cons children in
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Vari(x)    ->
              begin
                try
                  let id = VarMap.find x vars_id in
                  let cons = TC.Vari(id) in
                  let matched = TCMap.find cons children in
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Abst(_, b) ->
              begin
                match abstraction with
                | None        -> default ()
                | Some(id,tr) ->
                    let bound, body = Bindlib.unbind b in
                    let vars_id = VarMap.add bound id vars_id in
                    let id_vars = IntMap.add id bound id_vars in
                    let stk = List.reconstruct left (body::args) right in
                    walk tr stk cursor vars_id id_vars
              end
          | Meta(_, _) -> default ()
          | _          -> assert false
  in
  walk tree stk 0 VarMap.empty IntMap.empty

(** [snf t] computes the strong normal form of the term [t]. *)
and snf : term -> term = fun t ->
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

(** [whnf t] computes a weak head-normal form of [t]. *)
let whnf : term -> term = fun t ->
  Pervasives.(steps := 0);
  let t = unfold t in
  let u = whnf t in
  if Pervasives.(!steps = 0) then t else u

(** [simplify t] reduces simple redexes of [t]. *)
let rec simplify : term -> term = fun t ->
  match get_args (whnf t) with
  | Prod(a,b), _ ->
     let x,b = Bindlib.unbind b in
     Prod (simplify a, Bindlib.unbox (Bindlib.bind_var x (lift (simplify b))))
  | h, ts -> add_args h (List.map whnf_beta ts)

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
