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

(** Logging function for evaluation. *)
let log_eval = Logger.make 'e' "eval" "evaluation"
let log_eval = log_eval.pp

(** Logging function for equality modulo rewriting. *)
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
    if Logger.log_enabled () then log_eval "snf %a" term t;
    let h = whnf t in
    match h with
    | Vari _
    | Type
    | Kind
    | Symb _ -> h
    | LLet(_,t,b) -> snf (subst b t)
    | Prod(a,b) ->
      Prod(snf a, let x,b = unbind b in bind_var x (snf b))
    | Abst(a,b) ->
      Abst(snf a, let x,b = unbind b in bind_var x (snf b))
    | Appl(t,u)   -> Appl(snf t, snf u)
    | Meta(m,ts)  -> Meta(m, Array.map snf ts)
    | Patt(i,n,ts) -> Patt(i,n,Array.map snf ts)
    | Plac _      -> h (* may happen when reducing coercions *)
    | Bvar _      -> assert false
    | Wild        -> assert false
    | TRef _      -> assert false
  in snf

type rw_tag = [ `NoBeta | `NoRw | `NoExpand ]

(** Configuration of the reduction engine. *)
module Config = struct

  type t =
    { varmap : term VarMap.t (** Variable definitions. *)
    ; rewrite : bool (** Whether to apply user-defined rewriting rules. *)
    ; expand_defs : bool (** Whether to expand definitions. *)
    ; beta : bool (** Whether to beta-normalise *)
    ; dtree : sym -> dtree (** Retrieves the dtree of a symbol *) }

  (** [make ?dtree ?rewrite c] creates a new configuration with
      tags [?rewrite] (being empty if not provided), context [c] and
      dtree map [?dtree] (defaulting to getting the dtree from the symbol).
      By default, beta reduction and rewriting is enabled for all symbols. *)
  let make : ?dtree:(sym -> dtree) -> ?tags:rw_tag list -> ctxt -> t =
  fun ?(dtree=fun sym -> Timed.(!(sym.sym_dtree))) ?(tags=[]) context ->
    let beta = not @@ List.mem `NoBeta tags in
    let expand_defs = not @@ List.mem `NoExpand tags in
    let rewrite = not @@ List.mem `NoRw tags in
    {varmap = Ctxt.to_map context; rewrite; expand_defs; beta; dtree}

end

type config = Config.t

(** [insert t ts] inserts [t] in [ts] assuming that [ts] is in increasing
    order wrt [Term.comp]. *)
let insert t =
  let rec aux ts =
    match ts with
    | t1::ts when cmp t t1 > 0 -> t1::aux ts
    | _ -> t::ts
  in aux

(** [aliens f whnf cfg ts] computes the f-aliens of [ts]. f-aliens are in whnf
    and ordered in increasing order wrt [Term.comp]. *)
let aliens f whnf cfg =
  let rec aliens acc ts =
    match ts with
    | [] -> acc
    | t::ts -> aux acc t ts
  and aux acc t ts =
    match get_args t with
    | Symb g, [u1;u2] when g == f -> aux acc u1 (u2::ts)
    | _ ->
        let n = !steps in
        let t' = whnf cfg t in
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

(** [left_comb whnf cfg (+) [t1;t2;t3]] computes [whnf(whnf(t1+t2)+t3)]. *)
let left_comb s whnf cfg =
  let rec comb acc ts =
    match ts with
    | [] -> acc
    | t::ts -> comb (whnf cfg (app2 s acc t)) ts
  in
  function
  | [] | [_] -> assert false
  | t::ts -> comb t ts

(** [right_comb whnf cfg (+) [t1;t2;t3]] computes [whnf(t1+whnf(t2+t3))]. *)
let right_comb s whnf cfg =
  let rec comb ts acc =
    match ts with
    | [] -> acc
    | t::ts -> comb ts (whnf cfg (app2 s t acc))
  in
  fun ts ->
  match List.rev ts with
  | [] | [_] -> assert false
  | t::ts -> comb ts t

(** [comb s whnf cfg ts] computes the [whnf] of the comb obtained by applying
    [s] to [ts]. *)
let comb s =
  match s.sym_prop with
  | AC Left -> left_comb s
  | AC Right -> right_comb s
  | _ -> assert false

(** [ac whnf cfg t] computes a whnf of [t] in head-AC canonical form. *)
let ac whnf cfg t =
  let t = whnf cfg t in
  match get_args t with
  | Symb f, ([_;_] as ts) when is_ac f ->
      (*if Logger.log_enabled() then log_conv "ac_whnf %a" term t;*)
      comb f whnf cfg (aliens f whnf cfg ts)
  | _ -> t

(** [eq_modulo whnf cfg a b] tests the convertibility of [a] and [b] using
    [whnf]. *)
let eq_modulo : (config -> term -> term) -> config -> term eq = fun whnf ->
  let rec eq : config -> (term * term) list -> unit = fun cfg l ->
    match l with
    | [] -> ()
    | (a,b)::l ->
    if Logger.log_enabled () then
      log_conv "eq: %a ≡ %a %a" term a term b (D.list (D.pair term term)) l;
    (* We first check equality modulo alpha. *)
    if LibTerm.eq_alpha a b then eq cfg l else
    (* FIXME? Instead of computing the whnf of each side right away, we could
       perhaps do it more incrementally (the reduction of beta-redexes, let's
       and local definitions as done in whnf could be integrated here) and,
       when both heads are function symbols, use an heuristic like in Matita
       to decide which side to unfold first. Note also that, when comparing
       two AC symbols, we could detect the non-equivalence more quickly by
       testing the equality of the number of aliens:

    | (Symb f,([_;_]as ts)), (Symb g,([_;_]as us)) when is_ac f && g == f ->
        let ts = aliens f whnf cfg ts and us = aliens f whnf cfg us in
        let a = comb f whnf cfg ts and b = comb f whnf cfg us in
        let ts = comb_aliens f a and us = comb_aliens f b in
        if List.length ts <> List.length us then raise Exit
        else eq cfg (List.rev_append2 ts us l) *)
    let whnf t = (*Logger.set_debug_in "c" false (fun () ->*) ac whnf cfg t in
    let a = whnf a and b = whnf b in
    if Logger.log_enabled () then log_conv "whnf: %a ≡ %a" term a term b;
    match a, b with
    | Patt(None,_,_), _ | _, Patt(None,_,_) -> assert false
    | Patt(Some i,_,ts), Patt(Some j,_,us) ->
      if i=j then eq cfg (List.add_array2 ts us l) else raise Exit
    | Kind, Kind
    | Type, Type -> eq cfg l
    | Vari x, Vari y when eq_vars x y -> eq cfg l
    | Symb f, Symb g when f == g -> eq cfg l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = unbind2 b1 b2 in eq cfg ((a1,a2)::(b1,b2)::l)
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when Timed.(!eta_equality) ->
      let x,b = unbind b in eq cfg ((b, Appl(t, Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq cfg (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | Bvar _, _ | _, Bvar _ -> assert false
    | Appl(t1,u1), Appl(t2,u2) -> eq cfg ((u1,u2)::(t1,t2)::l)
    | _ -> raise Exit
  in
  fun cfg a b ->
  try eq cfg [(a,b)]; true
  with Exit -> if Logger.log_enabled () then log_conv "failed"; false

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

(** [whnf cfg t] computes a whnf of the term [t] wrt configuration [c]. *)
let rec whnf : config -> term -> term = fun cfg t ->
  let n = Stdlib.(!steps) in
  let u, stk = whnf_stk cfg t [] in
  if Stdlib.(!steps) <> n then add_args u stk else unfold t

(** [whnf_stk cfg t stk] computes a whnf of [add_args t stk] wrt
    configuration [c]. *)
and whnf_stk : config -> term -> stack -> term * stack = fun cfg t stk ->
  let t = unfold t in
  match t, stk with
  | Appl(f,u), stk -> whnf_stk cfg f (to_tref u::stk)
  | _ ->
  if Logger.log_enabled () then
    log_eval "%awhnf_stk %a %a" D.depth !depth term t (D.list term) stk;
  match t, stk with
  | Abst(_,f), u::stk when cfg.Config.beta ->
    Stdlib.incr steps; whnf_stk cfg (subst f u) stk
  | LLet(_,t,u), stk ->
      let x,u = unbind u in
      whnf_stk {cfg with varmap = VarMap.add x t cfg.varmap} u stk
  | (Symb s as h, stk) as r ->
    begin match Timed.(!(s.sym_def)) with
      (* The invariant that defined symbols are subject to no
         rewriting rules is false during indexing for websearch;
         that's the reason for the when in the next line *)
    | Some t when Tree_type.is_empty (cfg.dtree s) ->
      if Timed.(!(s.sym_opaq)) || not cfg.Config.expand_defs then r else
        (Stdlib.incr steps; whnf_stk cfg t stk)
    | None when not cfg.Config.rewrite -> r
    | _ ->
      match tree_walk cfg (cfg.dtree s) stk with
      | None -> h, stk
      | Some (t', stk') ->
        if Logger.log_enabled () then
          log_eval "%aapply rewrite rule" D.depth !depth;
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
    {!constructor:Term.term.TRef}). *)
and tree_walk : config -> dtree -> stack -> (term * stack) option =
  fun cfg tree stk ->
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
              if incr_depth (fun () -> eq_modulo whnf cfg vars.(i) vars.(j))
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
          let (t, args) = incr_depth (fun () -> whnf_stk cfg examined []) in
          let args = if store then List.map to_tref args else args in
          (* If some reduction has been performed by [whnf_stk] ([steps <>
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
          | TRef(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | Appl(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | LLet(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | Bvar _     -> assert false
          | Wild       -> assert false (* Should not appear in terms. *)
  in
  walk tree stk 0 VarMap.empty IntMap.empty

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
  let u = snf (whnf (Config.make ?dtree ?tags c)) t in
  if Stdlib.(!steps = 0) then unfold t else u

let snf ?dtree = time_reducer (snf ?dtree)

(** [hnf c t] computes a hnf of [t], unfolding the variables defined in the
    context [c], and using user-defined rewrite rules. *)
let hnf : reducer = fun ?tags c t ->
  Stdlib.(steps := 0);
  let u = hnf (whnf (Config.make ?tags c)) t in
  if Stdlib.(!steps = 0) then unfold t else u

let hnf = time_reducer hnf

(** [eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c]. WARNING: may have side effects in TRef's introduced by whnf. *)
let eq_modulo : ?tags:rw_tag list -> ctxt -> term -> term -> bool =
  fun ?tags c -> eq_modulo whnf (Config.make ?tags c)

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
  let u = ac whnf (Config.make ?tags c) t in
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
      let cfg = Config.make [] and dt = Timed.(!(s.sym_dtree)) in
      let unfold_sym_app args =
        match tree_walk cfg dt args with
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
