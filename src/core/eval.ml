(** Evaluation and conversion. *)

open Lplib open Base open Extra
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

(** Logging function for whnf. *)
let log_whnf = Logger.make 'w' "whnf" "whnf"
let log_whnf = log_whnf.pp

(** Logging function for snf. *)
let log_snf = Logger.make 'e' "snf " "snf"
let log_snf = log_snf.pp

(** Logging function for conversion. *)
let log_conv = Logger.make 'c' "conv" "conversion"
let log_conv = log_conv.pp

(** Convert modulo eta. *)
let eta_equality : bool Timed.ref = Console.register_flag "eta_equality" false

(** Counter used to preserve physical equality in {!val:whnf}. *)
let steps : int Stdlib.ref = Stdlib.ref 0

(** {1 Define reduction functions parametrised by {!whnf}} *)

(** [hnf whnf t] computes a hnf of [t] using [whnf]. *)
let hnf : (term -> term) -> (term -> term) = fun whnf ->
  let rec hnf t =
    match whnf t with
    | Abst(a,t) -> Abst(a, let x,t = unbind t in bind_var x (hnf t))
    | t -> t
  in hnf

(** [snf whnf t] computes a snf of [t] using [whnf]. *)
let snf : (term -> term) -> (term -> term) = fun whnf ->
  let rec snf t =
    if Logger.log_enabled() then log_snf "snf %a" term t;
    let t = whnf t in
    if Logger.log_enabled() then log_snf "whnf = %a" term t;
    match t with
    | Vari _
    | Type
    | Kind
    | Symb _
    | Plac _ (* may happen when reducing coercions *)
      -> t
    | LLet(_,t,b) -> snf (subst b t)
    | Prod(a,b) ->
      Prod(snf a, let x,b = unbind b in bind_var x (snf b))
    | Abst(a,b) ->
      Abst(snf a, let x,b = unbind b in bind_var x (snf b))
    | Appl(t,u)   -> Appl(snf t, snf u)
    | Meta(m,ts)  -> Meta(m, Array.map snf ts)
    | Patt(i,n,ts) -> Patt(i,n,Array.map snf ts)
    | Bvar _      -> assert false
    | Wild        -> assert false
    | TRef _      -> assert false
  in snf

(** [eq_modulo norm a b] tests the convertibility of [a] and [b] by comparing
    their [norm] forms. *)
let eq_modulo : (term -> term) -> term eq = fun norm ->
  let rec eq : (term * term) list -> unit = fun l ->
    match l with
    | [] -> ()
    | (a,b)::l ->
    if Logger.log_enabled () then
      log_conv "eq_modulo %a ≡ %a %a"
        term a term b (D.list (D.pair term term)) l;
    (* We first check equality modulo alpha. *)
    if LibTerm.eq_alpha a b then eq l else
    (* FIXME? Instead of computing the norm of each side right away, we could
       perhaps do it more incrementally (the reduction of beta-redexes, let's
       and local definitions as done in whnf could be integrated here) and,
       when both heads are function symbols, use an heuristic like in Matita
       to decide which side to unfold first.

       Note also that, when comparing two AC symbols, we could detect the
       non-equivalence more quickly by testing the equality of the number of
       aliens:

    | (Symb f,([_;_]as ts)), (Symb g,([_;_]as us)) when is_ac f && g == f ->
        let ts = aliens f norm ts and us = aliens f norm us in
        let a = comb f norm ts and b = comb f norm us in
        let ts = comb_aliens f a and us = comb_aliens f b in
        if List.length ts <> List.length us then raise Exit
        else eq (List.rev_append2 ts us l) *)
    let a = norm a and b = norm b in
    if Logger.log_enabled () then
      log_conv "eq_modulo after norm %a ≡ %a" term a term b;
    match a, b with
    | Patt(None,_,_), _ | _, Patt(None,_,_) -> assert false
    | Patt(Some i,_,ts), Patt(Some j,_,us) ->
      if i=j then eq (List.add_array2 ts us l) else raise Exit
    | Kind, Kind
    | Type, Type -> eq l
    | Vari x, Vari y when eq_vars x y -> eq l
    | Symb f, Symb g when f == g -> eq l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = unbind2 b1 b2 in eq ((a1,a2)::(b1,b2)::l)
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when Timed.(!eta_equality) ->
      let x,b = unbind b in eq ((b, Appl(t, Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | Bvar _, _ | _, Bvar _ -> assert false
    | Appl(t1,u1), Appl(t2,u2) -> eq ((u1,u2)::(t1,t2)::l)
    | _ -> raise Exit
  in
  fun a b ->
  try eq [(a,b)]; true
  with Exit -> if Logger.log_enabled () then log_conv "failed"; false

(** Reduction permissions. *)
type rw_tag = [ `NoRw | `NoExpand ]

(** Configuration of the reduction engine. *)
type config =
  { varmap : term VarMap.t (** Variable definitions. *)
  ; rewrite : bool (** Whether to apply user-defined rewriting rules. *)
  ; expand_defs : bool (** Whether to expand definitions. *)
  ; dtree : sym -> dtree (** Retrieves the dtree of a symbol *) }

(** [make ?dtree ?rewrite c] creates a new configuration with tags [?rewrite]
    (being empty if not provided), context [c] and dtree map [?dtree]
    (defaulting to getting the dtree from the symbol). By default, beta
    reduction and rewriting is enabled for all symbols. *)
let make : ?dtree:(sym -> dtree) -> ?tags:rw_tag list -> ctxt -> config =
  fun ?(dtree=fun sym -> Timed.(!(sym.sym_dtree))) ?(tags=[]) context ->
  let expand_defs = not @@ List.mem `NoExpand tags in
  let rewrite = not @@ List.mem `NoRw tags in
  {varmap = Ctxt.to_map context; rewrite; expand_defs; dtree}

(** Abstract machine stack. *)
type stack = term list

(** [to_tref t] transforms {!constructor:Appl} into
   {!constructor:TRef}. *)
let to_tref : term -> term = fun t ->
  match t with
  | Appl _ -> TRef(Timed.ref(Some t))
  | Symb s when s.sym_prop <> Const -> TRef(Timed.ref(Some t))
  | t -> t

(** {1 Define the main {!whnf} function that takes a {!config} as argument} *)
let depth = Stdlib.ref 0

let incr_depth f = incr depth; let v = f() in decr depth; v

(** [tree_walk norm dt stk] tries to apply a rewrite rule by matching the
    stack [stk] against the decision tree [dt], possibly reducing stack
    elements with [norm]. The resulting state of the abstract machine is
    returned in case of success. Even if matching fails, the stack [stk] may
    be imperatively updated since a reduction step taken in elements of the
    stack is preserved (this is done using {!constructor:Term.term.TRef}). *)
let tree_walk : (term -> term) -> dtree -> stack -> (term * stack) option =
  fun norm tree stk ->
  if Logger.log_enabled () then
    log_whnf "%atree_walk %a" D.depth !depth (D.list term) stk;
  let (lazy capacity, lazy tree) = tree in
  let vars = Array.make capacity Kind in (* dummy terms *)
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
          env.(i) <- Some(bind_mvar [||] (Plac false))
        done;
        Some (subst_patt env r.rhs, stk)
    | Cond({ok; cond; fail})                              ->
        let next =
          match cond with
          | CondNL(i, j) ->
              if incr_depth (fun () -> eq_modulo norm vars.(i) vars.(j))
              then ok else fail
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
              let b = bind_mvar allowed (snf norm vars.(i)) in
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
          let (t, args) = incr_depth (fun () -> get_args (norm examined)) in
          let args = if store then List.map to_tref args else args in
          (* If some reduction has been performed by [norm] ([steps <>
             0]), update the value of [examined] which may be stored into
             [vars]. *)
          if Stdlib.(!steps) <> s then
            begin
              match examined with
              | TRef(v) -> Timed.(v := Some(add_args t args))
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
          | TRef(_)    -> assert false (* Should be reduced by [norm]. *)
          | Appl(_)    -> assert false (* Should be reduced by [norm]. *)
          | LLet(_)    -> assert false (* Should be reduced by [norm]. *)
          | Bvar _     -> assert false
          | Wild       -> assert false (* Should not appear in terms. *)
  in
  walk tree stk 0 VarMap.empty IntMap.empty

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

(** [insert t ts] inserts [t] in [ts] assuming that [ts] is in increasing
    order wrt [Term.comp]. *)
let insert t =
  let rec aux ts =
    match ts with
    | t1::ts when cmp t t1 > 0 -> t1::aux ts
    | _ -> t::ts
  in aux

(** [aliens f norm ts] computes the f-aliens of [ts]. f-aliens are normalized
    wrt [norm] and ordered in increasing order wrt [Term.comp]. *)
let aliens f norm =
  let rec aliens acc ts =
    match ts with
    | [] -> acc
    | t::ts -> aux acc t ts
  and aux acc t ts =
    match get_args t with
    | Symb g, [u1;u2] when g == f -> aux acc u1 (u2::ts)
    | _ ->
        let n = !steps in
        let t' = norm t in
        if !steps = n then aliens (insert t acc) ts
        else aux acc t' ts
  in aliens []

(*
(** [left_comb_aliens f t] computes the aliens of [t] assuming that [t] is a
    left comb. *)
let left_comb_aliens f =
  let rec aliens acc t =
    match get_args t with
    | Symb g, [t1;t2] when g == f -> aliens (t2::acc) t1
    | _ -> t::acc
  in aliens []

(** [right_comb_aliens f t] computes the aliens of [t] assuming that [t] is a
    right comb. *)
let right_comb_aliens f =
  let rec aliens acc t =
    match get_args t with
    | Symb g, [t1;t2] when g == f -> aliens (t1::acc) t2
    | _ -> t::acc
  in aliens []

(** [comb_aliens f t] computes the aliens of [t] assuming that [t] is a
    comb. *)
let comb_aliens f =
  match f.sym_prop with
  | AC Left -> left_comb_aliens f
  | AC Right -> right_comb_aliens f
  | _ -> assert false
*)

(** [app2 s t1 t2] builds the application of [s] to [t1] and [t2]. *)
let app2 s t1 t2 = Appl(Appl(Symb s, t1), t2)

(** [left_comb norm (+) [t1;t2;t3]] computes [norm(norm(t1+t2)+t3)]. *)
let left_comb s norm =
  let rec comb acc ts =
    match ts with
    | [] -> acc
    | t::ts -> comb (norm (app2 s acc t)) ts
  in
  function
  | [] | [_] -> assert false
  | t::ts -> comb t ts

(** [right_comb norm (+) [t1;t2;t3]] computes [norm(t1+norm(t2+t3))]. *)
let right_comb s norm =
  let rec comb ts acc =
    match ts with
    | [] -> acc
    | t::ts -> comb ts (norm (app2 s t acc))
  in
  fun ts ->
  match List.rev ts with
  | [] | [_] -> assert false
  | t::ts -> comb ts t

(** [comb s norm ts] computes the [norm]-form of the comb obtained by applying
    [s] to [ts]. *)
let comb s =
  match s.sym_prop with
  | AC Left -> left_comb s
  | AC Right -> right_comb s
  | _ -> assert false

(** [sym_norm s t] computes the normal form of [t] wrt [s] rules. *)
let sym_norm s =
  let rec norm ((h,ts) as v) =
    match h with
    | Symb s' when s' == s ->
        begin
          match tree_walk (fun t -> t) Timed.(!(s.sym_dtree)) ts with
          | None -> v
          | Some v ->
              if Logger.log_enabled () then
                log_whnf "%aapply rewrite rule" D.depth !depth;
              Stdlib.incr steps; norm v
        end
    | _ -> v
  in
  fun t ->
  if Logger.log_enabled() then
    log_whnf "%asym_norm %a" D.depth !depth term t;
  let h,ts = norm (get_args t) in add_args h ts

(** [ac norm t] computes a head-AC [norm] form. *)
let ac norm t =
  let t = norm t in
  match get_args t with
  | Symb f, ([t1;t2] as ts) ->
      begin match f.sym_prop with
      | AC _ -> comb f norm (aliens f norm ts)
      | Commu when cmp t1 t2 > 0 -> app2 f t2 t1
      | _ -> t
      end
  | _ -> t

(** If [t] is headed by an AC symbol, then [ac norm t] computes its head-AC
    [norm] form. *)
let _new_ac t =
  match get_args t with
  | Symb s, ([t1;t2] as ts) ->
      begin match s.sym_prop with
      | AC _ -> comb s (sym_norm s) (aliens s (fun t -> t) ts)
      | Commu when cmp t1 t2 > 0 -> app2 s t2 t1
      | _ -> t
      end
  | _ -> t

(** If [t] is headed by a sequential symbol, then [seq norm t] computes a
    [norm] form of [t] so that each immediate subterm is also in [seq norm]
    form. Otherwise, [seq norm t = norm t]. *)
let rec seq norm t =
  match get_args t with
  | Symb s, _ when s.sym_mstrat = Sequen ->
      begin
        let t = norm t in
        let h, ts = get_args t in
        match h with
        | Symb _ -> add_args_map h (seq norm) ts
        | _ -> t
      end
  | _ -> norm t

(** [whnf cfg t] computes a whnf of the term [t] wrt configuration [cfg]. *)
let whnf : config -> term -> term = fun cfg ->
  (* [whnf t] computes a whnf of [t]. *)
  let rec whnf t =
    let n = Stdlib.(!steps) in
    let u, stk = whnf_stk t [] in
    if Stdlib.(!steps) <> n then add_args u stk else unfold t

  (* [whnf_stk t stk] computes a whnf of [add_args t stk]. *)
  and whnf_stk : term -> stack -> term * stack = fun t stk ->
    if Logger.log_enabled () then
      log_whnf "%awhnf_stk %a %a" D.depth !depth term t (D.list term) stk;
    let t = unfold t in
    match t with
    | Appl(f,u) -> whnf_stk f (to_tref u::stk)
    (*| _ ->
      if Logger.log_enabled() then
      log_whnf "%awhnf_stk %a %a" D.depth !depth term t (D.list term) stk;
      match t, stk with*)
    | Abst(_,f) ->
        begin
          match stk with
          | u::stk -> Stdlib.incr steps; whnf_stk (subst f u) stk
          | _ -> t, stk
        end
    | LLet(_,t,u) ->
        (*FIXME? instead of doing a substitution now, add a local definition
          instead to postpone the substitution when it will be necessary. But
          the following makes tests/OK/725.lp fail: *)
        (*let x,u = unbind u in
          whnf_stk {cfg with varmap = VarMap.add x t cfg.varmap} u stk*)
        Stdlib.incr steps; whnf_stk (subst u t) stk
    | Symb s ->
        begin match Timed.(!(s.sym_def)) with
        (* The invariant that defined symbols are subject to no
           rewriting rules is false during indexing for websearch;
           that's the reason for the when in the next line *)
        | Some u when Tree_type.is_empty (cfg.dtree s) ->
            if Timed.(!(s.sym_opaq)) || not cfg.expand_defs then t, stk
            else (Stdlib.incr steps; whnf_stk u stk)
        | None when not cfg.rewrite -> t, stk
        | _ ->
            let norm =
              (*if Timed.(!(s.sym_rstrat)) = Innermost then
                fun t -> new_ac (seq whnf t)
              else*) whnf
            in
            match tree_walk norm (cfg.dtree s) stk with
            | None -> t, stk
            | Some (t, stk) ->
                if Logger.log_enabled () then
                  log_whnf "%aapply rewrite rule" D.depth !depth;
                Stdlib.incr steps; whnf_stk t stk
        end
    | Vari x ->
        begin match VarMap.find_opt x cfg.varmap with
        | Some v -> Stdlib.incr steps; whnf_stk v stk
        | None -> t, stk
        end
    | _ -> t, stk
(*
  (* [snf t] computes snf of [t]. *)
  and snf t =
    let n = Stdlib.(!steps) in
    let u, stk = snf_stk t [] in
    if Stdlib.(!steps) <> n then add_args u stk else unfold t

  (* [snf_stk t stk] computes a snf of [add_args t stk]. *)
  and snf_stk : term -> stack -> term * stack = fun t stk ->
    if Logger.log_enabled () then
      log_whnf "%asnf_stk %a %a" D.depth !depth term t (D.list term) stk;
    let t = unfold t in
    match t with
    | Appl(f,u) -> snf_stk f (to_tref u::stk)
    (*| _ ->
      if Logger.log_enabled() then
      log_snf "%asnf_stk %a %a" D.depth !depth term t (D.list term) stk;
      match t, stk with*)
    | Abst(a,b) ->
        begin
          match stk with
          | u::stk when cfg.beta -> Stdlib.incr steps; snf_stk (subst b u) stk
          | _ -> Abst(snf a, binder snf b), List.map snf stk
        end
    | LLet(_,t,u) ->
        (*FIXME? instead of doing a substitution now, add a local definition
          instead to postpone the substitution when it will be necessary. But
          the following makes tests/OK/725.lp fail: *)
        (*let x,u = unbind u in
          snf_stk {cfg with varmap = VarMap.add x t cfg.varmap} u stk*)
        Stdlib.incr steps; snf_stk (subst u t) stk
    | Symb s ->
        begin match Timed.(!(s.sym_def)) with
        (* The invariant that defined symbols are subject to no
           rewriting rules is false during indexing for websearch;
           that's the reason for the when in the next line *)
        | Some u when Tree_type.is_empty (cfg.dtree s) ->
            if Timed.(!(s.sym_opaq)) || not cfg.expand_defs then
              t, List.map snf stk
            else (Stdlib.incr steps; snf_stk u stk)
        | None when not cfg.rewrite -> t, List.map snf stk
        | _ ->
            match tree_walk whnf (cfg.dtree s) stk with
            | None -> t, List.map snf stk
            | Some (t', stk') ->
                if Logger.log_enabled () then
                  log_snf "%aapply rewrite rule" D.depth !depth;
                Stdlib.incr steps; snf_stk t' stk'
        end
    | Vari x ->
        begin match VarMap.find_opt x cfg.varmap with
        | Some v -> Stdlib.incr steps; snf_stk v stk
        | None -> t, List.map snf stk
        end
    | Prod(a,b) -> Prod(snf a, binder snf b), stk
    | Type -> t, stk
    | Kind -> t, stk
    | Plac _ -> t, stk (* may happen when reducing coercions *)
    | Meta(m,ts) -> Meta(m,Array.map snf ts), List.map snf stk
    | Patt(i,n,ts) -> Patt(i,n,Array.map snf ts), List.map snf stk
    | Bvar _ -> assert false
    | Wild -> assert false
    | TRef _ -> assert false
 *)
  in fun t -> ac whnf (seq whnf t)

(** {1 Define exposed functions}
    that take optional arguments rather than a config. *)

type reducer = ?tags:rw_tag list -> ctxt -> term -> term

let time_reducer (f: reducer): reducer =
  let open Stdlib in let r = ref Kind in fun ?tags cfg t ->
    Debug.(record_time Rewriting (fun () -> r := f ?tags cfg t)); !r

(** [snf ~dtree c t] computes a snf of [t], unfolding the variables defined in
    the context [c]. The function [dtree] maps symbols to dtrees. *)
let snf : ?dtree:(sym -> dtree) -> reducer = fun ?dtree ?tags c t ->
  Stdlib.(steps := 0);
  let u = snf (whnf (make ?dtree ?tags c)) t in
  if Stdlib.(!steps = 0) then unfold t else u

let snf ?dtree = time_reducer (snf ?dtree)

(** [hnf c t] computes a hnf of [t], unfolding the variables defined in the
    context [c], and using user-defined rewrite rules. *)
let hnf : reducer = fun ?tags c t ->
  Stdlib.(steps := 0);
  let u = hnf (whnf (make ?tags c)) t in
  if Stdlib.(!steps = 0) then unfold t else u

let hnf = time_reducer hnf

(** [eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c]. WARNING: may have side effects in TRef's introduced by whnf. *)
let eq_modulo : ?tags:rw_tag list -> ctxt -> term -> term -> bool =
  fun ?tags c -> eq_modulo (whnf (make ?tags c))

let eq_modulo =
  let open Stdlib in let r = ref false in fun ?tags c t u ->
  Debug.(record_time Rewriting (fun () -> r := eq_modulo ?tags c t u)); !r

(** [pure_eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c] with no side effects. *)
let pure_eq_modulo : ?tags:rw_tag list -> ctxt -> term -> term -> bool =
  fun ?tags c a b ->
  Timed.pure_test
    (fun (c,a,b) ->
      ((*Logger.set_debug_in "ce" false (fun () ->*) eq_modulo ?tags c a b))
    (c,a,b)

(** [whnf c t] computes a whnf of [t], unfolding the variables defined in the
   context [c], and using user-defined rewrite rules if [~rewrite]. *)
let whnf : reducer = fun ?tags c t ->
  Stdlib.(steps := 0);
  let u = whnf (make ?tags c) t in
  if Stdlib.(!steps = 0) then unfold t else u

let whnf = time_reducer whnf

(** [simplify c t] computes a beta whnf of [t] in context [c] belonging to the
    set S such that (1) terms of S are in beta whnf normal format, (2) if [t]
    is a product, then both its domain and codomain are in S. *)
let simplify : ctxt -> term -> term = fun c ->
  let tags = [`NoRw; `NoExpand] in
  let rec simp t =
    match get_args (whnf ~tags c t) with
    | Prod(a,b), _ ->
       let x, b = unbind b in
       Prod (simp a, bind_var x (simp b))
    | h, ts -> add_args_map h (whnf ~tags c) ts
  in simp

let simplify =
  let open Stdlib in let r = ref Kind in fun c t ->
  Debug.(record_time Rewriting (fun () -> r := simplify c t)); !r

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
            | Abst(a,b) -> Abst(unfold_sym a, unfold_sym_binder b)
            | Prod(a,b) -> Prod(unfold_sym a, unfold_sym_binder b)
            | Meta(m,ts) -> Meta(m, Array.map unfold_sym ts)
            | LLet(a,t,u) ->
                LLet(unfold_sym a, unfold_sym t, unfold_sym_binder u)
            | _ -> h
          in add_args h args
    and unfold_sym_binder b =
      let x, b = unbind b in bind_var x (unfold_sym b)
    in unfold_sym
  in
  fun s ->
  if Timed.(!(s.sym_opaq)) then fun t -> t else
  match Timed.(!(s.sym_def)) with
  | Some d -> unfold_sym s (add_args d)
  | None ->
  match Timed.(!(s.sym_rules)) with
  | [] -> fun t -> t
  | _ ->
      let unfold_sym_app args =
        match tree_walk (whnf []) Timed.(!(s.sym_dtree)) args with
        | Some(r,ts) -> add_args r ts
        | None -> add_args (Symb s) args
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

(** [eval s c t] evaluates the term [t] in the context [c] according to
    strategy [s]. *)
let eval : strat -> ctxt -> term -> term = fun s c t ->
  match s.strategy, s.steps with
  | _, Some 0
  | NONE, _ -> t
  | WHNF, None -> whnf c t
  | SNF, None -> snf c t
  | HNF, None -> hnf c t
  (* TODO implement the rest. *)
  | _, Some _ -> wrn None "Number of steps not supported."; t
