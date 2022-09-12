(** Evaluation and conversion. *)

open Lplib open Extra
open Timed
open Common open Error open Debug
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
let log_eval = Logger.make 'e' "eval" "evaluation"
let log_eval = log_eval.pp

(** Logging function for equality modulo rewriting. *)
let log_conv = Logger.make 'c' "conv" "conversion"
let log_conv = log_conv.pp

(** Convert modulo eta. *)
let eta_equality : bool ref = Console.register_flag "eta_equality" false

(** Counter used to preserve physical equality in {!val:whnf}. *)
let steps : int Stdlib.ref = Stdlib.ref 0

(** {1 Define reduction functions parametrised by {!whnf}} *)

(** [hnf whnf t] computes a hnf of [t] using [whnf]. *)
let hnf : (term -> term) -> (term -> term) = fun whnf ->
  let rec hnf t =
    match whnf t with
    | Abst(a,t) ->
      let x, t = unbind t in mk_Abst(a, bind_var x (hnf t))
    | t -> t
  in hnf

(** [snf whnf t] computes a snf of [t] using [whnf]. *)
let snf : (term -> term) -> (term -> term) = fun whnf ->
  let rec snf t =
    if Logger.log_enabled () then log_eval "snf %a" term t;
    let h = whnf t in
    if Logger.log_enabled () then log_eval "whnf %a = %a" term t term h;
    match h with
    | Vari _
    | Type
    | Kind
    | Symb _ -> h
    | LLet(_,t,b) -> snf (subst b t)
    | Prod(a,b) ->
      let x, b = unbind b in
      mk_Prod(snf a, bind_var x (snf b))
    | Abst(a,b) ->
      let x, b = unbind b in
      mk_Abst(snf a, bind_var x (snf b))
    | Appl(t,u)   -> mk_Appl(snf t, snf u)
    | Meta(m,ts)  -> mk_Meta(m, Array.map snf ts)
    | Patt(i,n,ts) -> mk_Patt(i,n,Array.map snf ts)
    | Plac _      -> h (* may happen when reducing coercions *)
    | Db _ -> assert false
    | Wild        -> assert false
    | TRef(_)     -> assert false
  in snf

type rw_tag = [ `NoBeta | `NoRw | `NoExpand ]

(** Configuration of the reduction engine. *)
module Config = struct

  type t =
    { context : ctxt
    (** Context of the reduction used for generating metas. *)
    ; varmap : term VarMap.t (** Variable definitions. *)
    ; rewrite : bool (** Whether to apply user-defined rewriting rules. *)
    ; expand_defs : bool (** Whether to expand definitions. *)
    ; beta : bool (** Whether to beta-normalise *)
    ; problem : problem (** Generated metavariables. *) }

  (** [make ?problem ?rewrite c] creates a new configuration with problem
      [?problem] (being new if not provided), tags [?rewrite] (being empty if
      not provided) and context [c]. By default, beta reduction and rewriting
      is enabled for all symbols. *)
  let make : ?problem:problem -> ?tags:rw_tag list -> ctxt -> t =
  fun ?(problem=new_problem ()) ?(tags=[]) context ->
    let beta = not @@ List.mem `NoBeta tags in
    let expand_defs = not @@ List.mem `NoExpand tags in
    let rewrite = not @@ List.mem `NoRw tags in
    {context; varmap = Ctxt.to_map context; rewrite; expand_defs;
     beta; problem}

  (** [unfold cfg a] unfolds [a] if it's a variable defined in the
      configuration [cfg]. *)
  let rec unfold : t -> term -> term = fun cfg a ->
    match Term.unfold a with
    | Vari x as a->
      begin match VarMap.find_opt x cfg.varmap with
        | None -> a
        | Some v -> unfold cfg v
      end
    | a -> a

end

type config = Config.t

(** [eq_modulo whnf a b] tests the convertibility of [a] and [b] using
    [whnf]. *)
let eq_modulo : (config -> term -> term) -> config -> term -> term -> bool =
  fun whnf ->
  let rec eq : config -> (term * term) list -> unit = fun cfg l ->
    match l with
    | [] -> ()
    | (a,b)::l ->
    if Logger.log_enabled () then log_conv "eq: %a ≡ %a" term a term b;
    let a = Config.unfold cfg a and b = Config.unfold cfg b in
    if a == b then eq cfg l else
    match a, b with
    | LLet(_,t,u), _ ->
      let x,u = unbind u in
      eq {cfg with varmap = VarMap.add x t cfg.varmap} ((u,b)::l)
    | _, LLet(_,t,u) ->
      let x,u = unbind u in
      eq {cfg with varmap = VarMap.add x t cfg.varmap} ((a,u)::l)
    | Patt(None,_,_), _ | _, Patt(None,_,_) -> assert false
    | Patt(Some i,_,ts), Patt(Some j,_,us) ->
      if i=j then eq cfg (List.add_array2 ts us l) else raise Exit
    | Db i, Db j -> if i=j then eq cfg l else raise Exit
    | Kind, Kind
    | Type, Type -> eq cfg l
    | Vari x, Vari y -> if eq_vars x y then eq cfg l else raise Exit
    | Symb f, Symb g when f == g -> eq cfg l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = unbind2 b1 b2 in eq cfg ((a1,a2)::(b1,b2)::l)
    | Abst _, (Type|Kind|Prod _)
    | (Type|Kind|Prod _), Abst _ -> raise Exit
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when !eta_equality ->
      let x,b = unbind b in eq cfg ((b, mk_Appl(t, mk_Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq cfg (if a1 == a2 then l else List.add_array2 a1 a2 l)
    (* cases of failure *)
    | Kind, _ | _, Kind
    | Type, _ | _, Type -> raise Exit
    | ((Symb f, (Vari _|Meta _|Prod _|Abst _|Db _))
      | ((Vari _|Meta _|Prod _|Abst _|Db _), Symb f)) when is_constant f ->
      raise Exit
    | _ ->
    let a = whnf cfg a and b = whnf cfg b in
    if Logger.log_enabled () then log_conv "whnf: %a ≡ %a" term a term b;
    match a, b with
    | Patt(None,_,_), _ | _, Patt(None,_,_) -> assert false
    | Patt(Some i,_,ts), Patt(Some j,_,us) ->
      if i=j then eq cfg (List.add_array2 ts us l) else raise Exit
    | Db i, Db j -> if i=j then eq cfg l else raise Exit
    | Kind, Kind
    | Type, Type -> eq cfg l
    | Vari x, Vari y when eq_vars x y -> eq cfg l
    | Symb f, Symb g when f == g -> eq cfg l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = unbind2 b1 b2 in eq cfg ((a1,a2)::(b1,b2)::l)
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when !eta_equality ->
      let x,b = unbind b in eq cfg ((b, mk_Appl(t, mk_Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq cfg (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | Appl(t1,u1), Appl(t2,u2) -> eq cfg ((u1,u2)::(t1,t2)::l)
    | _ -> raise Exit
  in
  fun cfg a b ->
  if Logger.log_enabled () then log_conv "eq_modulo: %a ≡ %a" term a term b;
  try eq cfg [(a,b)]; true
  with Exit -> if Logger.log_enabled () then log_conv "failed"; false

(** Abstract machine stack. *)
type stack = term list

(** [to_tref t] transforms {!constructor:Appl} into
   {!constructor:TRef}. *)
let to_tref : term -> term = fun t ->
  match t with
  | Appl _ -> mk_TRef(ref (Some t))
  | Symb s when s.sym_prop <> Const -> mk_TRef(ref (Some t))
  | t -> t

(** {1 Define the main {!whnf} function that takes a {!config} as argument} *)

(** [whnf cfg t] computes a whnf of the term [t] wrt configuration [c]. *)
let rec whnf : config -> term -> term = fun cfg t ->
  (*if Logger.log_enabled () then log_eval "whnf %a" term t;*)
  let n = Stdlib.(!steps) in
  let u, stk = whnf_stk cfg t [] in
  let r = if Stdlib.(!steps) <> n then add_args u stk else unfold t in
  (*if Logger.log_enabled () then
    log_eval "whnf %a%a = %a" ctxt cfg.context term t term r;*)
  r

(** [whnf_stk cfg t stk] computes a whnf of [add_args t stk] wrt
    configuration [c]. *)
and whnf_stk : config -> term -> stack -> term * stack = fun cfg t stk ->
  (*if Logger.log_enabled () then
    log_eval "whnf_stk %a%a %a"
      ctxt cfg.context term t (D.list term) stk;*)
  let t = unfold t in
  match t, stk with
  | Appl(f,u), stk -> whnf_stk cfg f (to_tref u::stk)
  | Abst(_,f), u::stk when cfg.Config.beta ->
    Stdlib.incr steps; whnf_stk cfg (subst f u) stk
  | LLet(_,t,u), stk ->
    Stdlib.incr steps; whnf_stk cfg (subst u t) stk
  | (Symb s as h, stk) as r ->
    begin match !(s.sym_def) with
    | Some t ->
      if s.sym_opaq || not cfg.Config.expand_defs then r else
        (Stdlib.incr steps; whnf_stk cfg t stk)
    | None when not cfg.Config.rewrite -> r
    | None ->
      (* If [s] is modulo C or AC, we put its arguments in whnf and reorder
         them to have a term in AC-canonical form. *)
      let stk =
        if is_modulo s then
          let n = Stdlib.(!steps) in
          (* We put the arguments in whnf. *)
          let stk' = List.map (whnf cfg) stk in
          if Stdlib.(!steps) = n then (* No argument has been reduced. *)
            stk
          else (* At least one argument has been reduced. *)
            (* We put the term in AC-canonical form. *)
            snd (get_args (add_args h stk'))
        else stk
      in
      match tree_walk cfg !(s.sym_dtree) stk with
      | None -> h, stk
      | Some (t', stk') ->
        if Logger.log_enabled () then
          log_eval "tree_walk %a%a %a = %a %a" ctxt cfg.context
            term t (D.list term) stk term t' (D.list term) stk';
        Stdlib.incr steps; whnf_stk cfg t' stk'
    end
  | (Vari x, stk) as r ->
    begin match VarMap.find_opt x cfg.varmap with
    | Some v -> Stdlib.incr steps; whnf_stk cfg v stk
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

(** [tree_walk cfg dt stk] tries to apply a rewrite rule by matching the stack
    [stk] against the decision tree [dt].  The resulting state of the abstract
    machine is returned in case of success.  Even if matching fails, the stack
    [stk] may be imperatively updated since a reduction step taken in elements
    of the stack is preserved (this is done using
    {!constructor:Term.term.TRef}). Fresh metavariables generated by
    unification rules with extra pattern variables are added to
    the problem of [c]. *)
and tree_walk : config -> dtree -> stack -> (term * stack) option =
  fun cfg tree stk ->
  let (lazy capacity, lazy tree) = tree in
  let vars = Array.make capacity mk_Kind in (* dummy terms *)
  let bound = Array.make capacity None in
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
    | Leaf(rhs_subst, r) -> (* Apply the RHS substitution *)
        (* Allocate an environment where to place terms coming from the
           pattern variables for the action. *)
        assert (List.length rhs_subst = r.vars_nb);
        let env_len = r.vars_nb + r.xvars_nb in
        let env = Array.make env_len None in
        (* Retrieve terms needed in the action from the [vars] array. *)
        let f (pos, (slot, xs)) =
          match bound.(pos) with
          | Some(_) -> env.(slot) <- bound.(pos)
          | None    ->
                let xs = Array.map (fun e -> IntMap.find e id_vars) xs in
                env.(slot) <- Some(bind_mvar xs vars.(pos))
        in
        List.iter f rhs_subst;
        (* Complete the array with fresh meta-variables if needed. *)
        for i = r.vars_nb to env_len - 1 do
          env.(i) <- Some(bind_mvar [||] (mk_Plac false))
        done;
        Some (subst_patt env r.rhs, stk)
    | Cond({ok; cond; fail})                              ->
        let next =
          match cond with
          | CondNL(i, j) ->
            if eq_modulo whnf cfg vars.(i) vars.(j) then ok else fail
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
                not (IntMap.exists (fun _ x -> occur_mbinder x b)
                       forbidden)
              in
              (* We first attempt to match [vars.(i)] directly. *)
              let b = bind_mvar allowed vars.(i) in
              if no_forbidden b
              then (bound.(i) <- Some b; ok) else
              (* As a last resort we try matching the SNF. *)
              let b = bind_mvar allowed (snf (whnf cfg) vars.(i)) in
              if no_forbidden b
              then (bound.(i) <- Some b; ok)
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
          Option.bind default fn
        else
          let s = Stdlib.(!steps) in
          let (t, args) = whnf_stk cfg examined [] in
          let args = if store then List.map to_tref args else args in
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
            Option.bind default fn
          in
          (* [walk_binder a  b  id tr]  matches  on  binder  [b]  of type  [a]
             introducing variable  [id] and branching  on tree [tr].  The type
             [a] and [b] substituted are re-inserted in the stack.*)
          let walk_binder a b id tr =
            let (bound, body) = unbind b in
            let vars_id = VarMap.add bound id vars_id in
            let id_vars = IntMap.add id bound id_vars in
            let stk = List.reconstruct left (a::body::args) right in
            walk tr stk cursor vars_id id_vars
          in
          match t with
          | Type       ->
              begin
                try
                  let matched = TCMap.find TC.Type children in
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
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
          | Patt _
          | Meta(_, _) -> default ()
          | Plac _     -> assert false
             (* Should not appear in typechecked terms. *)
          | TRef(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | Appl(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | LLet(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | Db _ -> assert false
          | Wild       -> assert false (* Should not appear in terms. *)
  in
  walk tree stk 0 VarMap.empty IntMap.empty

(** {1 Define exposed functions}
    that take optional arguments rather than a config. *)

type reducer = ?problem:problem -> ?tags:rw_tag list -> ctxt -> term -> term

let time_reducer (f: reducer): reducer =
  let open Stdlib in let r = ref mk_Kind in fun ?problem ?tags cfg t ->
    Debug.(record_time Rewriting (fun () -> r := f ?problem ?tags cfg t)); !r

(** [snf c t] computes a snf of [t], unfolding the variables defined in the
    context [c]. *)
let snf : reducer = fun ?problem ?tags c t ->
  Stdlib.(steps := 0);
  let u = snf (whnf (Config.make ?problem ?tags c)) t in
  let r = if Stdlib.(!steps = 0) then unfold t else u in
  (*if Logger.log_enabled () then
    log_eval "snf %a%a\n= %a" ctxt cfg term t term r;*) r

let snf = time_reducer snf

(** [hnf c t] computes a hnf of [t], unfolding the variables defined in the
    context [c], and using user-defined rewrite rules. *)
let hnf : reducer = fun ?problem ?tags c t ->
  Stdlib.(steps := 0);
  let u = hnf (whnf (Config.make ?problem ?tags c)) t in
  let r = if Stdlib.(!steps = 0) then unfold t else u in
  (*if Logger.log_enabled () then
    log_eval "hnf %a%a\n= %a" ctxt cfg term t term r;*) r

let hnf = time_reducer hnf

(** [eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c]. WARNING: may have side effects in TRef's introduced by whnf. *)
let eq_modulo : ctxt -> term -> term -> bool = fun c ->
  eq_modulo whnf (Config.make c)

let eq_modulo =
  let open Stdlib in let r = ref false in fun c t u ->
  Debug.(record_time Rewriting (fun () -> r := eq_modulo c t u)); !r

(** [pure_eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c] with no side effects. *)
let pure_eq_modulo : ctxt -> term -> term -> bool = fun c a b ->
  Timed.pure_test (fun (c,a,b) -> eq_modulo c a b) (c,a,b)

(** [whnf c t] computes a whnf of [t], unfolding the variables defined in the
   context [c], and using user-defined rewrite rules if [~rewrite]. *)
let whnf : reducer = fun ?problem ?tags c t ->
  Stdlib.(steps := 0);
  let u = whnf (Config.make ?problem ?tags c) t in
  let r = if Stdlib.(!steps = 0) then unfold t else u in
  (*if Logger.log_enabled () then
    log_eval "whnf %a%a\n= %a" ctxt c term t term r;*)
  r

let whnf = time_reducer whnf

(** [simplify t] computes a beta whnf of [t] belonging to the set S such that:
- terms of S are in beta whnf normal format
- if [t] is a product, then both its domain and codomain are in S. *)
let rec simplify : term -> term = fun t ->
  let tags = [`NoRw; `NoExpand ] in
  match get_args (whnf ~tags [] t) with
  | Prod(a,b), _ ->
     let x, b = unbind b in
     mk_Prod (simplify a, bind_var x (simplify b))
  | h, ts -> add_args_map h (whnf ~tags []) ts

let simplify =
  let open Stdlib in let r = ref mk_Kind in fun t ->
  Debug.(record_time Rewriting (fun () -> r := simplify t)); !r

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
      let x, b = unbind b in bind_var x (unfold_sym b)
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
      let cfg = Config.make [] and dt = !(s.sym_dtree) in
      let unfold_sym_app args =
        match tree_walk cfg dt args with
        | Some(r,ts) -> add_args r ts
        | None -> add_args (mk_Symb s) args
      in unfold_sym s unfold_sym_app

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
