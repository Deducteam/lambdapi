(** Evaluation and conversion. *)

open! Lplib
open Lplib.Extra

open Timed
open Console
open Terms
open Basics
open Print

(** The head-structure of a term t is:
- λx:_,h if t=λx:a,u and h is the head-structure of u
- Π if t=Πx:a,u
- h _ if t=uv and h is the head-structure of u
- ? if t=?M[t1,..,tn] (and ?M is not instantiated)
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
let steps : int Stdlib.ref = Stdlib.ref 0

(** [appl_to_tref t] transforms {!constructor:Appl} into references. *)
let appl_to_tref : term -> term = fun t ->
  match t with
  | Appl(_,_) as t -> TRef(ref (Some t))
  | t              -> t

(** Abstract machine stack. *)
type stack = term list

(** [whnf_beta t] computes a weak head beta normal form of the term [t]. *)
let rec whnf_beta : term -> term = fun t ->
  if !log_enabled then log_eval "evaluating %a" pp_term t;
  let s = Stdlib.(!steps) in
  let (u, stk) = whnf_beta_stk t [] in
  if Stdlib.(!steps) <> s then add_args u stk else unfold t

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
      Stdlib.incr steps;
      whnf_beta_stk (Bindlib.subst f u) stk
  (* In head beta normal form. *)
  | (_        , _      ) -> st

(** [whnf_beta t] computes a weak head beta normal form of [t]. *)
let whnf_beta : term -> term = fun t ->
  Stdlib.(steps := 0);
  let u = whnf_beta t in
  if Stdlib.(!steps = 0) then unfold t else u

(** [whnf ctx t] computes a weak head normal form of the term [t] in context
    [ctx]. *)
let rec whnf : ctxt -> term -> term = fun ctx t ->
  if !log_enabled then log_eval "evaluating [%a]" pp_term t;
  let s = Stdlib.(!steps) in
  let (u, stk) = whnf_stk ctx t [] in
  if Stdlib.(!steps) <> s then add_args u stk else Ctxt.unfold ctx t

(** [whnf_stk ctx t stk] computes the weak head normal form of [t] applied to
    stack [stk] in context [ctx]. Note that the normalisation is done in the
    sense of [whnf]. *)
and whnf_stk : ctxt -> term -> stack -> term * stack = fun ctx t stk ->
  let st = (Ctxt.unfold ctx t, stk) in
  match st with
  (* Push argument to the stack. *)
  | (Appl(f,u), stk   ) ->
      whnf_stk ctx f (appl_to_tref u::stk)
  (* Beta reduction. *)
  | (Abst(_,f), u::stk) ->
      Stdlib.incr steps;
      whnf_stk ctx (Bindlib.subst f u) stk
  (* Let unfolding *)
  | (LLet(_,t,u), stk ) ->
      Stdlib.incr steps;
      whnf_stk ctx (Bindlib.subst u t) stk
  (* Try to rewrite. *)
  | (Symb(s), stk     ) ->
      begin
      (* First check for symbol definition. *)
      match !(s.sym_def) with
      | Some(t) -> Stdlib.incr steps; whnf_stk ctx t stk
      | None    ->
      (* Otherwise try rewriting using decision tree. *)
      match tree_walk !(s.sym_tree) ctx stk with
      (* If no rule is found, return the original term *)
      | None        -> st
      | Some(t,stk) -> Stdlib.incr steps; whnf_stk ctx t stk
      end
  (* In head normal form. *)
  | (_         , _    ) -> st

(** [eq_modulo ctx a b] tests the equality of [a] and [b] modulo rewriting and
    the unfolding of variables from the context [ctx] (δ-reduction). *)
and eq_modulo : ctxt -> term -> term -> bool = fun ctx a b ->
  if !log_enabled then log_conv "%a" pp_constr (ctx,a,b);
  let rec eq_modulo l =
    match l with
    | []       -> ()
    | (a,b)::l ->
    let a = unfold a and b = unfold b in
    if a == b then eq_modulo l else
    match (whnf ctx a, whnf ctx b) with
    | (Patt(_,_,_), _          )
    | (_          , Patt(_,_,_))
    | (TEnv(_,_)  , _          )
    | (_          , TEnv(_,_)  ) -> assert false
    | (Kind       , Kind       )
    | (Type       , Type       ) -> eq_modulo l
    | (Vari(x)    , Vari(y)    ) when Bindlib.eq_vars x y -> eq_modulo l
    | (Symb(s1)   , Symb(s2)   ) when s1 == s2 -> eq_modulo l
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
  if !log_enabled then log_conv (r_or_g res "%a") pp_constr (ctx,a,b); res

(** {b NOTE} that in {!val:tree_walk} matching with trees involves two
    collections of terms.
    1. The argument stack [stk] of type {!type:stack} which contains the terms
       that are matched against the decision tree.
    2. An array [vars] of variables that are used for non-linearity checks and
       free variable checks, or that are used in the RHS.

    The [bound] array is similar to the [vars] array except that it is used to
    save terms with free variables. *)

(** {b NOTE} in the {!val:tree_walk} function, bound variables involve three
    elements:
    1. a {!constructor:Terms.term.Abst} which introduces the bound variable in
       the term;
    2. a {!constructor:Terms.term.Vari} which is the bound variable previously
       introduced;
    3. a {!constructor:Tree_types.TC.t.Vari} which is a simplified
       representation of a variable for trees. *)

(** [tree_walk tr ctx stk] tries to apply a rewrite rule by matching the stack
    [stk] against the decision tree [tr] in context [ctx]. The resulting state
    of the abstract machine  is returned in case of success.  Even if matching
    fails,  the stack [stk] may be imperatively updated since a reduction step
    taken in elements of the stack is preserved (this is done using
    {!constructor:Terms.term.TRef}). *)
and tree_walk : dtree -> ctxt -> stack -> (term * stack) option =
  fun tree ctx stk ->
  let (lazy capacity, lazy tree) = tree in
  let vars = Array.make capacity Kind in (* dummy terms *)
  let bound = Array.make capacity TE_None in
  (* [walk tree stk cursor vars_id id_vars] where [stk] is the stack of terms
     to match and [cursor] the cursor indicating where to write in the [vars]
     array described in {!module:Terms} as the environment of the RHS during
     matching. [vars_id] maps the free variables contained in the term to the
     indexes defined during tree build, and [id_vars] is the inverse mapping
     of [vars_id]. *)
  let rec walk tree stk cursor vars_id id_vars =
    let open Tree_types in
    match tree with
    | Fail                                                -> None
    | Leaf(env_builder, (act, xvars))                     ->
        (* Allocate an environment where to place terms coming from the
           pattern variables for the action. *)
        let env_len = Bindlib.mbinder_arity act in
        assert (List.length env_builder = env_len - xvars);
        let env = Array.make env_len TE_None in
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
        (* Complete the array with fresh meta-variables if needed. *)
        for i = env_len - xvars to env_len - 1 do
          let mt = make_meta ctx Type in
          let t = make_meta ctx mt in
          let b = Bindlib.raw_mbinder [||] [||] 0 mkfree (fun _ -> t) in
          env.(i) <- TE_Some(b)
        done;
        Some (Bindlib.msubst act env, stk)
    | Cond({ok; cond; fail})                              ->
        let next =
          match cond with
          | CondNL(i, j) ->
              if eq_modulo [] vars.(i) vars.(j) then ok else fail
          | CondFV(i,xs) ->
              let allowed =
                (* Variables that are allowed in the term. *)
                let fn id =
                  try IntMap.find id id_vars with Not_found -> assert false
                in
                Array.map fn xs
              in
              let forbidden =
                (* Term variables forbidden in the term. *)
                IntMap.filter (fun id _ -> not (Array.mem id xs)) id_vars
              in
              (* Ensure there are no variables from [forbidden] in [b]. *)
              let no_forbidden b =
                not (IntMap.exists (fun _ x -> Bindlib.occur x b) forbidden)
              in
              (* We first attempt to match [vars.(i)] directly. *)
              let b = Bindlib.bind_mvar allowed (lift vars.(i)) in
              if no_forbidden b
              then (bound.(i) <- TE_Some(Bindlib.unbox b); ok) else
              (* As a last resort we try matching the SNF. *)
              let b = Bindlib.bind_mvar allowed (lift (snf ctx vars.(i))) in
              if no_forbidden b
              then (bound.(i) <- TE_Some(Bindlib.unbox b); ok)
              else fail
        in
        walk next stk cursor vars_id id_vars
    | Eos(l, r)                                                    ->
        let next = if stk = [] then l else r in
        walk next stk cursor vars_id id_vars
    | Node({swap; children; store; abstraction; default; product}) ->
        match List.destruct stk swap with
        | exception Not_found     -> None
        | (left, examined, right) ->
        if TCMap.is_empty children && abstraction = None && product = None
        (* If there is no specialisation tree, try directly default case. *)
        then
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
          let s = Stdlib.(!steps) in
          let (t, args) = whnf_stk ctx examined [] in
          let args = if store then List.map appl_to_tref args else args in
          (* If some reduction has been performed by [whnf_stk] ([steps <>
             0]), update the value of [examined] which may be stored into
             [vars]. *)
          if Stdlib.(!steps) <> s then
            begin
              match examined with
              | TRef(v) -> v := Some(add_args t args)
              | _       -> ()
            end;
          let cursor =
            if store then (vars.(cursor) <- add_args t args; cursor + 1)
            else cursor
          in
          (* [default ()] carries on the matching on the default branch of the
             tree. Nothing is added to the stack. *)
          let default () =
            let fn d =
              let stk = List.reconstruct left [] right in
              walk d stk cursor vars_id id_vars
            in
            Option.map_default fn None default
          in
          (* [walk_binder a  b  id tr]  matches  on  binder  [b]  of type  [a]
             introducing variable  [id] and branching  on tree [tr].  The type
             [a] and [b] substituted are re-inserted in the stack.*)
          let walk_binder a b id tr =
            let (bound, body) = Bindlib.unbind b in
            let vars_id = VarMap.add bound id vars_id in
            let id_vars = IntMap.add id bound id_vars in
            let stk = List.reconstruct left (a::body::args) right in
            walk tr stk cursor vars_id id_vars
          in
          match t with
          | Symb(s)    ->
              let cons = TC.Symb(s.sym_path, s.sym_name, List.length args) in
              begin
                try
                  (* Get the next sub-tree. *)
                  let matched = TCMap.find cons children in
                  (* Re-insert the arguments the symbol is applied to in the
                     stack. *)
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Vari(x)    ->
              begin
                try
                  let id = VarMap.find x vars_id in
                  let matched = TCMap.find (TC.Vari(id)) children in
                  (* Re-insert the arguments the variable is applied to in the
                     stack. *)
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Abst(a, b) ->
              begin
                match abstraction with
                | None        -> default ()
                | Some(id,tr) -> walk_binder a b id tr
              end
          | Prod(a, b) ->
              begin
                match product with
                | None        -> default ()
                | Some(id,tr) -> walk_binder a b id tr
              end
          | Kind
          | Type
          | Meta(_, _) -> default ()
          | TRef(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | Appl(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | LLet(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | Patt(_)    -> assert false (* Should not appear in terms. *)
          | TEnv(_)    -> assert false (* Should not appear in terms. *)
          | Wild       -> assert false (* Should not appear in terms. *)
  in
  walk tree stk 0 VarMap.empty IntMap.empty

(** [snf t] computes the strong normal form of the term [t]. *)
and snf : ctxt -> term -> term = fun ctx t ->
  let h = whnf ctx t in
  match h with
  | Vari(_)     -> h
  | Type        -> h
  | Kind        -> h
  | Symb(_)     -> h
  | LLet(_,t,b) -> snf ctx (Bindlib.subst b t)
  | Prod(a,b)   ->
      let (x,b) = Bindlib.unbind b in
      let b = snf ctx b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Prod(snf ctx a, b)
  | Abst(a,b)   ->
      let (x,b) = Bindlib.unbind b in
      let b = snf ctx b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Abst(snf ctx a, b)
  | Appl(t,u)   -> Appl(snf ctx t, snf ctx u)
  | Meta(m,ts)  -> Meta(m, Array.map (snf ctx) ts)
  | Patt(_,_,_) -> assert false
  | TEnv(_,_)   -> assert false
  | Wild        -> assert false
  | TRef(_)     -> assert false

(** [whnf t] computes a weak head-normal form of [t]. *)
let whnf : ctxt -> term -> term = fun ctx t ->
  Stdlib.(steps := 0);
  let u = whnf ctx t in
  if Stdlib.(!steps = 0) then unfold t else u

(** [simplify t] reduces simple redexes of [t]. *)
let rec simplify : ctxt -> term -> term = fun ctx t ->
  match get_args (whnf_beta t) with
  | Prod(a,b), _ ->
     let (x,b) = Bindlib.unbind b in
     let b = Bindlib.bind_var x (lift (simplify ctx b)) in
     Prod (simplify ctx a, Bindlib.unbox b)
  | h, ts -> add_args h (List.map whnf_beta ts)

(** [hnf t] computes a head-normal form of the term [t]. *)
let rec hnf : ctxt -> term -> term = fun ctx t ->
  match whnf ctx t with
  | Abst(a,t) ->
     let x,t = Bindlib.unbind t in
     Abst(a, Bindlib.unbox (Bindlib.bind_var x (lift (hnf ctx t))))
  | t         -> t

(** [eval cfg ctx t] evaluates the term [t] in the context [ctx] according to
    configuration [cfg]. *)
let eval : Syntax.eval_config -> ctxt -> term -> term = fun c ctx t ->
  match (c.strategy, c.steps) with
  | (_   , Some(0))
  | (NONE, _      ) -> t
  | (WHNF, None   ) -> whnf ctx t
  | (SNF , None   ) -> snf ctx t
  | (HNF , None   ) -> hnf ctx t
  (* TODO implement the rest. *)
  | (_   , Some(_)) -> wrn None "Number of steps not supported."; t

(** Equality function for two constraints *)
let eq_constr : constr -> constr -> bool = fun (ctx1,t1,u1) (ctx2,t2,u2) ->
  let t1,_ = Ctxt.to_abst ctx1 t1 in
  let u1,_ = Ctxt.to_abst ctx1 u1 in
  let t2,_ = Ctxt.to_abst ctx2 t2 in
  let u2,_ = Ctxt.to_abst ctx2 u2 in
  (eq_modulo [] t1 t2) && (eq_modulo [] u1 u2) ||
  (eq_modulo [] t1 u2) && (eq_modulo [] t2 u1)

(** Comparing function for two contraints. For the non equal case, we forward
    to the standard library compare function *)
let compare_constr : constr -> constr -> int = fun c1 c2 ->
  if eq_constr c1 c2 then 0 else Basics.cmp_constr c1 c2
