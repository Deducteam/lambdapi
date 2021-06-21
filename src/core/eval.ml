(** Evaluation and conversion. *)

open! Lplib
open Lplib.Extra
open Timed
open Common
open Error
open Debug
open Term
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

(** [hnf whnf t] computes a hnf of [t] using [whnf]. *)
let hnf : (term -> term) -> (term -> term) = fun whnf ->
  let rec hnf t =
    match whnf t with
    | Abst(a,t) ->
        let x, t = Bindlib.unbind t in
        mk_Abst(a, Bindlib.unbox (Bindlib.bind_var x (lift (hnf t))))
    | t -> t
  in hnf

(** [snf whnf t] computes a snf of [t] using [whnf]. *)
let snf : (term -> term) -> (term -> term) = fun whnf ->
  let rec snf t =
    if !log_enabled then log_eval "snf %a" pp_term t;
    let h = whnf t in
    if !log_enabled then log_eval "whnf %a = %a" pp_term t pp_term h;
    match h with
    | Vari _
    | Type
    | Kind
    | Symb _ -> h
    | LLet(_,t,b) -> snf (Bindlib.subst b t)
    | Prod(a,b) ->
        let x, b = Bindlib.unbind b in
        mk_Prod(snf a, Bindlib.unbox (Bindlib.bind_var x (lift (snf b))))
    | Abst(a,b) ->
        let x, b = Bindlib.unbind b in
        mk_Abst(snf a, Bindlib.unbox (Bindlib.bind_var x (lift (snf b))))
    | Appl(t,u)   -> mk_Appl(snf t, snf u)
    | Meta(m,ts)  -> mk_Meta(m, Array.map snf ts)
    | Patt(_,_,_) -> assert false
    | TEnv(_,_)   -> assert false
    | Wild        -> assert false
    | TRef(_)     -> assert false
  in snf

(** [Configuration of the reduction engine. *)
type config =
  { context : ctxt (** Context of the reduction used for generating metas. *)
  ; defmap : term VarMap.t (** Variable definitions. *)
  ; rewrite : bool (** Use user-defined rewrite rules. *)
  ; problem : problem (** Generated metavariables. *) }

(*let pp_defmap = D.map VarMap.iter pp_var " ≔ " pp_term "; "*)

let cfg_of_ctx : ctxt -> bool -> config = fun context rewrite ->
  {context; defmap = Ctxt.to_map context; rewrite; problem = new_problem()}

let unfold_cfg : config -> term -> term = fun c a ->
  let a = unfold a in
  match a with
  | Vari x ->
    begin match VarMap.find_opt x c.defmap with
      | None -> a
      | Some v -> unfold v
    end
  | _ -> a

(** [eq_modulo whnf a b] tests the convertibility of [a] and [b] using
    [whnf]. *)
let eq_modulo : (config -> term -> term) -> (config -> term -> term -> bool) =
  fun whnf ->
  let rec eq : config -> (term * term) list -> unit = fun c l ->
    match l with
    | [] -> ()
    | (a,b)::l ->
    (*if !log_enabled then log_conv "%a ≡ %a" pp_term a pp_term b;*)
    let a = unfold_cfg c a and b = unfold_cfg c b in
    if a == b then eq c l else
    match a, b with
    | LLet(_,t,u), _ ->
      let x,u = Bindlib.unbind u in
      eq {c with defmap = VarMap.add x t c.defmap} ((u,b)::l)
    | _, LLet(_,t,u) ->
      let x,u = Bindlib.unbind u in
      eq {c with defmap = VarMap.add x t c.defmap} ((a,u)::l)
    | Patt _, _ | _, Patt _
    | TEnv _, _| _, TEnv _ -> assert false
    | Kind, Kind
    | Type, Type -> eq c l
    | Vari x, Vari y -> if Bindlib.eq_vars x y then eq c l else raise Exit
    | Symb f, Symb g when f == g -> eq c l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = Bindlib.unbind2 b1 b2 in eq c ((a1,a2)::(b1,b2)::l)
    | Abst _, (Type|Kind|Prod _)
    | (Type|Kind|Prod _), Abst _ -> raise Exit
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when !eta_equality ->
      let x,b = Bindlib.unbind b in eq c ((b, mk_Appl(t, mk_Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq c (if a1 == a2 then l else List.add_array2 a1 a2 l)
    (* cases of failure *)
    | Kind, _ | _, Kind
    | Type, _ | _, Type
      -> raise Exit
    | ((Symb f, (Vari _|Meta _|Prod _|Abst _))
      | ((Vari _|Meta _|Prod _|Abst _), Symb f)) when is_constant f ->
      raise Exit
    | _ ->
    let a = whnf c a and b = whnf c b in
    (*if !log_enabled then log_conv "%a ≡ %a" pp_term a pp_term b;*)
    match a, b with
    | Patt _, _ | _, Patt _
    | TEnv _, _| _, TEnv _ -> assert false
    | Kind, Kind
    | Type, Type -> eq c l
    | Vari x, Vari y when Bindlib.eq_vars x y -> eq c l
    | Symb f, Symb g when f == g -> eq c l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = Bindlib.unbind2 b1 b2 in eq c ((a1,a2)::(b1,b2)::l)
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when !eta_equality ->
      let x,b = Bindlib.unbind b in eq c ((b, mk_Appl(t, mk_Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq c (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | Appl(t1,u1), Appl(t2,u2) -> eq c ((u1,u2)::(t1,t2)::l)
    | _ -> raise Exit
  in
  fun c a b ->
  if !log_enabled then log_conv "%a ≡ %a" pp_term a pp_term b;
  try eq c [(a,b)]; true
  with Exit -> if !log_enabled then log_conv "failed"; false

(** Abstract machine stack. *)
type stack = term list

(** [appl_to_tref t] transforms {!constructor:Appl} into
   {!constructor:TRef}. *)
let appl_to_tref : term -> term = fun t ->
  match t with
  | Appl _ -> mk_TRef(ref (Some t))
  | t -> t

(** [whnf c t] computes a whnf of the term [t] wrt configuration [c]. *)
let rec whnf : config -> term -> term = fun c t ->
  (*if !log_enabled then log_eval "whnf %a" pp_term t;*)
  let s = Stdlib.(!steps) in
  let u, stk = whnf_stk c t [] in
  let r = if Stdlib.(!steps) <> s then add_args u stk else unfold t in
  (*if !log_enabled then
    log_eval "whnf %a%a = %a" pp_ctxt c.context pp_term t pp_term r;*)
  r

(** [whnf_stk c t stk] computes a whnf of [add_args t stk] wrt
   configuration [c]. *)
and whnf_stk : config -> term -> stack -> term * stack = fun c t stk ->
  (*if !log_enabled then
    log_eval "whnf_stk %a%a %a"
      pp_ctxt c.context pp_term t (D.list pp_term) stk;*)
  let t = unfold t in
  match t, stk with
  | Appl(f,u), stk -> whnf_stk c f (appl_to_tref u::stk)
  | Abst(_,f), u::stk ->
    Stdlib.incr steps; whnf_stk c (Bindlib.subst f u) stk
  | LLet(_,t,u), stk ->
    Stdlib.incr steps; whnf_stk c (Bindlib.subst u t) stk
  | (Symb s, stk) as r when c.rewrite ->
    begin match !(s.sym_def) with
    | Some t ->
      if s.sym_opaq then r else (Stdlib.incr steps; whnf_stk c t stk)
    | None ->
      match tree_walk c !(s.sym_dtree) stk with
      | None -> r
      | Some(t',stk') ->
        if !log_enabled then
          log_eval "tree_walk %a%a %a = %a %a" pp_ctxt c.context
            pp_term t (D.list pp_term) stk pp_term t' (D.list pp_term) stk';
        Stdlib.incr steps; whnf_stk c t' stk'
    end
  | (Vari x, stk) as r ->
    begin match VarMap.find_opt x c.defmap with
    | Some v -> Stdlib.incr steps; whnf_stk c v stk
    | None -> r
    end
  | r -> r

(** {b NOTE} that in {!val:tree_walk} matching with trees involves two
    collections of terms.
    1. The argument stack [stk] of type {!type:stack} which contains the terms
       that are matched against the decision tree.
    2. An array [vars] containing subterms of the argument stack [stk] that
       are filtered by a pattern variable. These terms may be used for
       non-linearity or free-variable checks, or may be bound in the RHS.

    The [bound] array is similar to the [vars] array except that it is used to
    save terms with free variables. *)

(** {b NOTE} in the {!val:tree_walk} function, bound variables involve three
    elements:
    1. a {!constructor:Term.term.Abst} which introduces the bound variable in
       the term;
    2. a {!constructor:Term.term.Vari} which is the bound variable previously
       introduced;
    3. a {!constructor:Tree_type.TC.t.Vari} which is a simplified
       representation of a variable for trees. *)

(** [tree_walk dt m stk] tries to apply a rewrite rule by matching the stack
   [stk] against the decision tree [dt] using variable definitions in [m]. The
   resulting state of the abstract machine is returned in case of
   success. Even if matching fails, the stack [stk] may be imperatively
   updated since a reduction step taken in elements of the stack is preserved
   (this is done using {!constructor:Term.term.TRef}). Fresh metavariables
   generated by unification rules with extra pattern variables are added to
   [!the_problem]. *)
and tree_walk : config -> dtree -> stack -> (term * stack) option =
  fun c tree stk ->
  let (lazy capacity, lazy tree) = tree in
  let vars = Array.make capacity mk_Kind in (* dummy terms *)
  let bound = Array.make capacity TE_None in
  (* [walk tree stk cursor vars_id id_vars] where [stk] is the stack of terms
     to match and [cursor] the cursor indicating where to write in the [vars]
     array described in {!module:Term} as the environment of the RHS during
     matching. [vars_id] maps the free variables contained in the term to the
     indexes defined during tree build, and [id_vars] is the inverse mapping
     of [vars_id]. *)
  let rec walk tree stk cursor vars_id id_vars =
    let open Tree_type in
    match tree with
    | Fail -> None
    | Leaf(rhs_subst, (act, xvars)) -> (* Apply the RHS substitution *)
        (* Allocate an environment where to place terms coming from the
           pattern variables for the action. *)
        let env_len = Bindlib.mbinder_arity act in
        assert (List.length rhs_subst = env_len - xvars);
        let env = Array.make env_len TE_None in
        (* Retrieve terms needed in the action from the [vars] array. *)
        let f (pos, (slot, xs)) =
          match bound.(pos) with
          | TE_Vari(_) -> assert false
          | TE_Some(_) -> env.(slot) <- bound.(pos)
          | TE_None    ->
              if Array.length xs = 0 then
                let t = unfold vars.(pos) in
                let b = Bindlib.raw_mbinder [||] [||] 0 of_tvar (fun _ -> t)
                in env.(slot) <- TE_Some(b)
              else
                let b = lift vars.(pos) in
                let xs = Array.map (fun e -> IntMap.find e id_vars) xs in
                env.(slot) <- TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs b))
        in
        List.iter f rhs_subst;
        (* Complete the array with fresh meta-variables if needed. *)
        for i = env_len - xvars to env_len - 1 do
          let mt = LibMeta.make c.problem c.context mk_Type in
          let t = LibMeta.make c.problem c.context mt in
          let b = Bindlib.raw_mbinder [||] [||] 0 of_tvar (fun _ -> t) in
          env.(i) <- TE_Some(b)
        done;
        Some (Bindlib.msubst act env, stk)
    | Cond({ok; cond; fail})                              ->
        let next =
          match cond with
          | CondNL(i, j) ->
            if eq_modulo whnf c vars.(i) vars.(j) then ok else fail
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
              let b = Bindlib.bind_mvar allowed
                        (lift (snf (whnf c) vars.(i))) in
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
          Option.bind fn default
        else
          let s = Stdlib.(!steps) in
          let (t, args) = whnf_stk c examined [] in
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
            Option.bind fn default
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

(** [snf c t] computes a snf of [t], unfolding the variables defined in the
   context [c]. *)
let snf : ctxt -> term -> term = fun c t ->
  Stdlib.(steps := 0);
  let u = snf (whnf (cfg_of_ctx c true)) t in
  let r = if Stdlib.(!steps = 0) then unfold t else u in
  (*if !log_enabled then
    log_eval "snf %a%a\n= %a" pp_ctxt c pp_term t pp_term r;*) r

(** [hnf c t] computes a hnf of [t], unfolding the variables defined in the
   context [c], and using user-defined rewrite rules. *)
let hnf : ctxt -> term -> term = fun c t ->
  Stdlib.(steps := 0);
  let u = hnf (whnf (cfg_of_ctx c true)) t in
  let r = if Stdlib.(!steps = 0) then unfold t else u in
  (*if !log_enabled then
    log_eval "hnf %a%a\n= %a" pp_ctxt c pp_term t pp_term r;*) r

(** [eq_modulo c a b] tests the convertibility of [a] and [b] in context
   [c]. WARNING: may have side effects in TRef's introduced by whnf. *)
let eq_modulo : ctxt -> term -> term -> bool = fun c ->
  eq_modulo whnf (cfg_of_ctx c true)

(** [pure_eq_modulo c a b] tests the convertibility of [a] and [b] in context
   [c] with no side effects. *)
let pure_eq_modulo : ctxt -> term -> term -> bool = fun c a b ->
  Timed.pure_test (fun (c,a,b) -> eq_modulo c a b) (c,a,b)

(** [whnf c t] computes a whnf of [t], unfolding the variables defined in the
   context [c], and using user-defined rewrite rules if [~rewrite]. *)
let whnf : ?rewrite:bool -> ctxt -> term -> term = fun ?(rewrite=true) c t ->
  Stdlib.(steps := 0);
  let u = whnf (cfg_of_ctx c rewrite) t in
  let r = if Stdlib.(!steps = 0) then unfold t else u in
  (*if !log_enabled then
    log_eval "whnf %a%a\n= %a" pp_ctxt c pp_term t pp_term r;*) r

(** [simplify t] computes a beta whnf of [t] belonging to the set S such that:
- terms of S are in beta whnf normal format
- if [t] is a product, then both its domain and codomain are in S. *)
let rec simplify : term -> term = fun t ->
  match get_args (whnf ~rewrite:false [] t) with
  | Prod(a,b), _ ->
     let x, b = Bindlib.unbind b in
     let b = Bindlib.bind_var x (lift (simplify b)) in
     mk_Prod (simplify a, Bindlib.unbox b)
  | h, ts -> add_args_map h (whnf ~rewrite:false []) ts

(** If [s] is a non-opaque symbol having a definition, [unfold_sym s t]
   replaces in [t] all the occurrences of [s] by its definition. *)
let unfold_sym : sym -> term -> term =
  let unfold_sym : sym -> (term list -> term) -> term -> term =
    fun s unfold_sym_app ->
    let rec unfold_sym t =
      let h, args = get_args t in
      let args = List.map unfold_sym args in
      match h with
      | Symb s' when s' == s -> unfold_sym_app args
      | _ ->
          let h =
            match h with
            | Abst(a,b) -> mk_Abst(unfold_sym a, unfold_sym_binder b)
            | Prod(a,b) -> mk_Prod(unfold_sym a, unfold_sym_binder b)
            | Meta(m,ts) -> mk_Meta(m, Array.map unfold_sym ts)
            | LLet(a,t,u) ->
                mk_LLet(unfold_sym a, unfold_sym t, unfold_sym_binder u)
            | _ -> h
          in add_args h args
    and unfold_sym_binder b =
      let x, b = Bindlib.unbind b in
      Bindlib.unbox (Bindlib.bind_var x (lift (unfold_sym b)))
    in unfold_sym
  in
  fun s ->
  if s.sym_opaq then fun t -> t else
  match !(s.sym_def) with
  | Some d -> unfold_sym s (add_args d)
  | None ->
  match !(s.sym_rules) with
  | [] -> fun t -> t
  | _ ->
      let c = cfg_of_ctx [] true and dt = !(s.sym_dtree) in
      let unfold_sym_app args =
        match tree_walk c dt args with
        | Some(r,ts) -> add_args r ts
        | None -> add_args (mk_Symb s) args
      in unfold_sym s unfold_sym_app

(** [tree_walk p tr c stk] tries to apply a rewrite rule by matching the
   stack [stk] against the decision tree [tr] in context [c]. The resulting
   state of the abstract machine is returned in case of success. Even if
   matching fails, the stack [stk] may be imperatively updated since a
   reduction step taken in elements of the stack is preserved (this is done
   using {!constructor:Term.term.TRef}). Fresh metavariables generated by
   unification rules with extra pattern variables are added in [p]. *)
let tree_walk : problem -> ctxt -> dtree -> stack -> (term * stack) option =
  fun p c dt ts ->
  let c = {context=c; defmap=Ctxt.to_map c; problem=p; rewrite=true} in
  tree_walk c dt ts

(** Dedukti evaluation strategies. *)
type strategy =
  | WHNF (** Reduce to weak head-normal form. *)
  | HNF  (** Reduce to head-normal form. *)
  | SNF  (** Reduce to strong normal form. *)
  | NONE (** Do nothing. *)

type strat =
  { strategy : strategy   (** Evaluation strategy. *)
  ; steps    : int option (** Max number of steps if given. *) }

(** [eval cfg c t] evaluates the term [t] in the context [c] according to
    evaluation configuration [cfg]. *)
let eval : strat -> ctxt -> term -> term = fun s c t ->
  match s.strategy, s.steps with
  | _, Some 0
  | NONE, _ -> t
  | WHNF, None -> whnf c t
  | SNF, None -> snf c t
  | HNF, None -> hnf c t
  (* TODO implement the rest. *)
  | _, Some _ -> wrn None "Number of steps not supported."; t
