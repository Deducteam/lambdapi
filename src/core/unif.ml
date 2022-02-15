(** Solving unification constraints. *)

open Lplib open Color
open Timed
open Common open Error open Debug
open Term
open LibTerm
open Print

(** Logging function for unification. *)
let logger = Logger.make 'u' "unif" "unification"
let log = logger.pp

(** Given a meta [m] of type [Πx1:a1,..,Πxn:an,b], [set_to_prod p m] sets [m]
   to a product term of the form [Πy:m1[x1;..;xn],m2[x1;..;xn;y]] with [m1]
   and [m2] fresh metavariables, and adds these metavariables to [p]. *)
let set_to_prod : problem -> meta -> unit = fun p m ->
  let n = m.meta_arity in
  let env, s = Env.of_prod_nth [] n !(m.meta_type) in
  let vs = Env.vars env in
  let xs = Array.map mk_Vari vs in
  (* domain *)
  let u1 = Env.to_prod env mk_Type in
  let m1 = LibMeta.fresh p u1 n in
  let a = mk_Meta (m1, xs) in
  (* codomain *)
  let y = new_tvar "y" in
  let env' = Env.add "y" y (mk_Meta (m1, xs)) None env in
  let u2 = Env.to_prod env' s in
  let m2 = LibMeta.fresh p u2 (n+1) in
  let b = bind_var y (mk_Meta (m2, Array.append xs [|mk_Vari y|])) in
  (* result *)
  let r = mk_Prod (a, b) in
  if Logger.log_enabled () then
    log (red "%a ≔ %a") meta m term r;
  LibMeta.set p m (bind_mvar vs r)

(** [type_app c a ts] returns [Some u] where [u] is a type of [add_args x ts]
   in context [c] where [x] is any term of type [a] if [x] can be applied to
   at least [List.length ts] arguments, and [None] otherwise. *)
let rec type_app : ctxt -> term -> term list -> term option = fun c a ts ->
  match Eval.whnf c a, ts with
  | Prod(_,b), t::ts -> type_app c (subst b t) ts
  | _, [] -> Some a
  | _, _ -> None

(** [add_constr p c] adds the constraint [c] into [p.to_solve]. *)
let add_constr : problem -> constr -> unit = fun p c ->
  if Logger.log_enabled () then log (mag "add %a") constr c;
  p := {!p with to_solve = c::!p.to_solve}

(** [add_unif_rule_constr p (c,t,u)] adds to [p] the constraint [(c,t,u)]
    as well as the constraint [(c,a,b)] where [a] is the type of [t] and [b]
    the type of [u] if they can be infered. *)
let add_unif_rule_constr : problem -> constr -> unit = fun p (c,t,u) ->
  match Infer.infer_noexn p c t with
  | None ->
      Error.fatal_no_pos "@[Unification rule lead to an untypable term:@ %a@]"
        term t
  | Some (t, a) ->
      match Infer.infer_noexn p c u with
      | None ->
          Error.fatal_no_pos
            "@[Unification rule lead to an untypable term:@ %a@]"
            term u
      | Some (u, b) ->
          add_constr p (c, t, u);
          if not (Eval.pure_eq_modulo c a b) then add_constr p (c, a, b)

(** [try_unif_rules p c s t] tries to simplify the unification problem [c
   ⊢ s ≡ t] with the user-defined unification rules. *)
let try_unif_rules : problem -> ctxt -> term -> term -> bool =
  fun p c s t ->
  if Logger.log_enabled () then log "check unif_rules";
  let exception No_match in
  let open Unif_rule in
  try
    let rhs =
      let start = add_args (mk_Symb equiv) [s;t] in
      let reduced = Eval.whnf ~problem:p c start in
      if reduced != start then reduced else
        let start = add_args (mk_Symb equiv) [t;s] in
        let reduced = Eval.whnf ~problem:p c start in
        if reduced != start then reduced else raise No_match
    in
    let cs = List.map (fun (t,u) -> (c,t,u)) (unpack rhs) in
    if Logger.log_enabled () then log "rewrites to:%a" constrs cs;
    List.iter (add_unif_rule_constr p) cs;
    true
  with No_match ->
    if Logger.log_enabled () then log "found no unif_rule";
    false

(** [instantiable c m ts u] tells whether, in a problem [m[ts]=u], [m] can
   be instantiated. It does not check whether the instantiation is closed
   though. *)
let instantiable : ctxt -> meta -> term array -> term -> bool =
  fun c m ts u -> nl_distinct_vars c ts <> None && not (LibMeta.occurs m c u)

(** [instantiation c m ts u] tells whether, in a problem [m[ts]=u], [m] can
   be instantiated and returns the corresponding instantiation, simplified. It
   does not check whether the instantiation is closed though. *)
let instantiation :
      ctxt -> meta -> term array -> term -> tmbinder option =
  fun c m ts u ->
  match nl_distinct_vars c ts with
    | None -> None
    | Some(vs, map) ->
        if LibMeta.occurs m c u then None
        else let u = Eval.simplify (Ctxt.to_let c (sym_to_var map u)) in
          Some (Logger.set_debug_in false 'm' (bind_mvar vs) u)

(** Checking type or not during meta instanciation. *)
let do_type_check = Stdlib.ref true

(** [instantiate p c m ts u] checks whether, with a constraint [m[ts] ≡ u],
   [m] can be instantiated and, if so, instantiates it and updates the
   metavariables of [p]. *)
let instantiate : problem -> ctxt -> meta -> term array -> term -> bool =
  fun p c m ts u ->
  if Logger.log_enabled () then log "try instantiate";
  match instantiation c m ts u with
  | Some b when is_closed_tmbinder b ->
      let do_instantiate() =
        if Logger.log_enabled () then log (red "%a ≔ %a") meta m term u;
        LibMeta.set p m b;
        p := {!p with recompute = true}; true
      in
      if Stdlib.(!do_type_check) then
        begin
          if Logger.log_enabled () then log "check typing";
          let typ_mts =
            match type_app c !(m.meta_type) (Array.to_list ts) with
            | Some a -> a
            | None -> assert false
          in
          let r =
            Logger.set_debug_in false 'i' (Infer.check_noexn p c u) typ_mts
          in
          if r <> None then do_instantiate()
          else (if Logger.log_enabled () then log "typing failed"; false)
        end
      else do_instantiate()
  | i ->
      if Logger.log_enabled () then
        begin
          match i with
          | None ->
              if LibMeta.occurs m c u then log "occur check failed"
              else log "arguments are not distinct variables: %a"
                     (Array.pp term "; ") ts
          | Some _ -> log "not closed"
        end;
      false

(** [add_to_unsolved p c t1 t2] checks whether [t1] is equivalent to [t2] in
   context [c]. If not, then it tries to apply unification rules. If no
   unification rule applies then it adds [(c,t1,t2)] to the unsolved
   constraints of [p]. *)
let add_to_unsolved : problem -> ctxt -> term -> term -> unit =
  fun p c t1 t2 ->
  if Eval.pure_eq_modulo c t1 t2 then
    (if Logger.log_enabled () then log "equivalent terms")
  else if not (try_unif_rules p c t1 t2) then
    (if Logger.log_enabled () then log "move to unsolved";
     p := {!p with unsolved = (c,t1,t2)::!p.unsolved})

(** [decompose p c ts1 ts2] tries to decompose a problem of the form [h ts1 ≡
   h ts2] into the problems [t1 ≡ u1; ..; tn ≡ un], assuming that [ts1 =
   [t1;..;tn]] and [ts2 = [u1;..;un]]. *)
let decompose : problem -> ctxt -> term list -> term list -> unit =
  fun p c ts1 ts2 ->
    if Logger.log_enabled () && ts1 <> [] then log "decompose";
    List.iter2 (fun a b -> add_constr p (c,a,b)) ts1 ts2

(** For a problem of the form [h1 ≡ h2] with [h1 = m[ts]], [h2 = Πx:_,_] (or
   the opposite) and [ts] distinct bound variables, [imitate_prod p c m h1 h2
   p] instantiates [m] to a product and adds the constraint [h1 ≡ h2] to
   [p]. *)
let imitate_prod : problem -> ctxt -> meta -> term -> term -> unit =
  fun p c m h1 h2 ->
  if Logger.log_enabled () then log "imitate_prod %a" meta m;
  set_to_prod p m; add_constr p (c,h1,h2)

(** For a problem [m[vs] ≡ s(ts)] in context [c], where [vs] are distinct
   variables, [m] is a meta of type [Πy0:a0,..,Πyk-1:ak-1,b] with [k = length
   vs], [s] is an injective symbol of type [Πx0:b0,..,Πxn-1:bn-1,c] with [n =
   length ts], [imitate_inj p c m vs us s ts] tries to instantiate [m] by
   [s(m0[vs],..,mn-1[vs])] where [mi] is a fresh meta of type
   [Πv0:a0,..,Πvk-1:ak-1{y0=v0,..,yk-2=vk-2}, bi{x0=m0[vs],..,xi-1=mi-1[vs]}].
   It returns [true] if it can and [false] otherwise. *)
let imitate_inj :
      problem -> ctxt -> meta -> term array -> term list -> sym -> term list
      -> bool =
  fun p c m vs us s ts ->
  if Logger.log_enabled () then
    log "imitate_inj %a ≡ %a" term (add_args (mk_Meta(m,vs)) us)
                                   term (add_args (mk_Symb s) ts);
  let exception Cannot_imitate in
  try
    if us <> [] || not (is_injective s)
      || LibMeta.occurs m c (add_args (mk_Symb s) ts) then
      raise Cannot_imitate;
    let vars =
      match distinct_vars c vs with
      | None -> raise Cannot_imitate
      | Some vars -> vars
    in
    (* Build the environment (yk-1,ak-1{y0=v0,..,yk-2=vk-2});..;(y0,a0). *)
    let env, _ = Env.of_prod_using c vars !(m.meta_type) in
    (* Build the term s(m0[vs],..,mn-1[vs]). *)
    let k = Array.length vars in
    let t =
      let rec build i acc t =
        if i <= 0 then add_args (mk_Symb s) (List.rev acc) else
        match unfold t with
        | Prod(a,b) ->
            let m = LibMeta.fresh p (Env.to_prod env a) k in
            let u = mk_Meta (m,vs) in
            build (i-1) (u::acc) (subst b u)
        | _ -> raise Cannot_imitate
      in build (List.length ts) [] !(s.sym_type)
    in
    if Logger.log_enabled () then log (red "%a ≔ %a") meta m term t;
    LibMeta.set p m (bind_mvar vars t); true
  with Cannot_imitate | Invalid_argument _ -> false

(** [imitate_lam_cond h ts] tells whether [ts] is headed by a variable not
   occurring in [h]. *)
let imitate_lam_cond : term -> term list -> bool = fun h ts ->
  match ts with
  | [] -> false
  | e :: _ ->
      match unfold e with
      | Vari x -> not (occur x h)
      | _ -> false

(** For a problem of the form [Appl(m[ts],[Vari x;_]) ≡ _], where [m] is a
   metavariable of arity [n] and type [Πx1:a1,..,Πxn:an,t], and [x] does not
   occur in [m[ts]], instantiate [m] by [λx1:a1,..,λxn:an,λx:a,m1[x1,..,xn,x]]
   where [m1] is a new metavariable of arity [n+1] and:

  - either [t = Πx:a,b] and [m1] is of type [Πx1:a1,..,Πxn:an,Πx:a,b]

  - or we add the problem [t ≡ Πx:m2[x1,..,xn],m3[x1,..,xn,x]] where [m2] is a
   new metavariable of arity [n] and type [Πx1:a1,..,Πxn:an,TYPE] and [m3] is
   a new metavariable of arity [n+1] and type
   [Πx1:a1,..,Πxn:an,Πx:m2[x1,..,xn],TYPE], and do as in the previous case. *)
let imitate_lam : problem -> ctxt -> meta -> unit = fun p c m ->
    if Logger.log_enabled () then log "imitate_lam %a" meta m;
    let n = m.meta_arity in
    let env, t = Env.of_prod_nth c n !(m.meta_type) in
    let of_prod a b =
      let x,b = LibTerm.unbind_name "x" b in
      let env' = Env.add "x" x a None env in
      x, a, env', b
    in
    let x, a, env', b =
      match Eval.whnf c t with
      | Prod(a,b) -> of_prod a b
      | Meta(n,ts) as t when nl_distinct_vars c ts <> None ->
          begin
            set_to_prod p n;
            match unfold t with
            | Prod(a,b) -> of_prod a b
            | _ -> assert false
          end
      | _ ->
         let tm2 = Env.to_prod env mk_Type in
         let m2 = LibMeta.fresh p tm2 n in
         let a = mk_Meta (m2, Env.to_terms env) in
         let x = new_tvar "x" in
         let env' = Env.add "x" x a None env in
         let tm3 = Env.to_prod env' mk_Type in
         let m3 = LibMeta.fresh p tm3 (n+1) in
         let b = mk_Meta (m3, Env.to_terms env') in
         let u = mk_Prod (a, bind_var x b) in
         add_constr p (Env.to_ctxt env, u, t);
         x, a, env', b
    in
    let tm1 = Env.to_prod env' b in
    let m1 = LibMeta.fresh p tm1 (n+1) in
    let u1 = mk_Meta (m1, Env.to_terms env') in
    let xu1 = mk_Abst (a, bind_var x u1) in
    let v = bind_mvar (Env.vars env) xu1 in
    if Logger.log_enabled () then
      log (red "%a ≔ %a") meta m term xu1;
    LibMeta.set p m v

(** [inverse_opt s ts v] returns [Some(t, inverse s v)] if [ts=[t]], [s] is
   injective and [inverse s v] does not fail, and [None] otherwise. *)
let inverse_opt : sym -> term list -> term -> (term * term) option =
  fun s ts v ->
  if Logger.log_enabled () then log "try inverse %a" sym s;
  try
    match ts with
    | [t] when is_injective s -> Some (t, Inverse.inverse s v)
    | _ -> raise Not_found
  with Not_found -> if Logger.log_enabled () then log "failed"; None

(** Exception raised when a constraint is not solvable. *)
exception Unsolvable

(** [error t1 t2]
@raise Unsolvable. *)
let error : term -> term -> 'a = fun t1 t2 ->
  fatal_msg "@[<hov>%a and %a are not unifiable.@]@."
    (D.bracket term) t1 (D.bracket term) t2;
  raise Unsolvable

(** [inverse p c t1 s ts1 t2] tries to replace a problem of the form [t1 ≡ t2]
   with [t1 = s(ts1)] and [ts1=[u]] by [u ≡ inverse s t2], when [s] is
   injective. *)
let inverse : problem -> ctxt -> term -> sym -> term list -> term -> unit =
  fun p c t1 s ts1 t2 ->
  match inverse_opt s ts1 t2 with
  | Some (t, u) -> add_constr p (c,t,u)
  | _ ->
      if not (try_unif_rules p c t1 t2) then
        match unfold t2 with
        | Prod _ when is_constant s -> error t1 t2
        | _ ->
            if Logger.log_enabled () then log "move to unsolved";
            p := {!p with unsolved = (c, t1, t2)::!p.unsolved}

(** [sym_sym_whnf p c t1 s1 ts1 t2 s2 ts2 p] handles the case [s1(ts1) =
   s2(ts2); p] when [s1(ts1)] and [s2(ts2)] are in whnf. *)
let sym_sym_whnf :
      problem -> ctxt -> term -> sym -> term list -> term -> sym -> term list
      -> unit =
  fun p c t1 s1 ts1 t2 s2 ts2 ->
  if s1 == s2 then
    if is_injective s1 then
      if List.same_length ts1 ts2 then decompose p c ts1 ts2
      else error t1 t2
    else add_to_unsolved p c t1 t2
  else
    if is_constant s1 && is_constant s2 then error t1 t2
    else match inverse_opt s1 ts1 t2 with
      | Some (t, u) -> add_constr p (c,t,u)
      | None -> inverse p c t2 s2 ts2 t1

(** [solve_noexn p] tries to simplify the constraints of [p].
@raise [Unsolvable] if it finds a constraint that cannot be satisfied.
Otherwise, [p.to_solve] is empty but [p.unsolved] may still contain
constraints that could not be simplified. *)
let solve : problem -> unit = fun p ->
  while !p.to_solve <> [] || (!p.recompute && !p.unsolved <> []) do
  match !p.to_solve with
  | [] ->
      if Logger.log_enabled () then log "recompute";
      p := {!p with to_solve = !p.unsolved; unsolved = []; recompute = false}
  | (c,t1,t2)::to_solve ->
  (*if Logger.log_enabled () then
    log "%d constraints" (1 + List.length to_solve);*)
  if Logger.log_enabled() then log "solve problem %a" problem p;

  (* We remove the first constraint from [p] for not looping. *)
  p := {!p with to_solve};

  (* We first try without normalizing wrt user-defined rules. *)
  let t1 = Eval.whnf ~tags:[`NoRw] c t1
  and t2 = Eval.whnf ~tags:[`NoRw] c t2 in
  if Logger.log_enabled () then log (gre "solve %a") constr (c,t1,t2);
  let h1, ts1 = get_args t1 and h2, ts2 = get_args t2 in

  match h1, h2 with
  | Type, Type
  | Kind, Kind -> ()

  | Prod(a1,b1), Prod(a2,b2)
  | Abst(a1,b1), Abst(a2,b2) ->
      (* [ts1] and [ts2] must be empty because of typing or normalization. *)
      if Logger.log_enabled () then log "decompose";
      add_constr p (c,a1,a2);
      let (x,b1,b2) = unbind2 b1 b2 in
      let c' = (x,a1,None)::c in
      add_constr p (c',b1,b2);

  | Vari x1, Vari x2 when eq_vars x1 x2 ->
      if List.same_length ts1 ts2 then decompose p c ts1 ts2
      else error t1 t2

  | Type, (Kind|Prod _|Symb _|Vari _|Abst _)
  | Kind, (Type|Prod _|Symb _|Vari _|Abst _)
  | Prod _, (Type|Kind|Vari _)
  | Vari _, (Type|Kind|Vari _|Prod _)
    -> error t1 t2

  | ((Vari _|Abst _|Prod _), Symb s
    | Symb s, (Type|Kind|Vari _|Abst _|Prod _)) when s.sym_prop = Const ->
    error t1 t2

  | Symb s1, Symb s2
       when s1 == s2 && is_injective s1 && List.same_length ts1 ts2 ->
      decompose p c ts1 ts2
  | Symb s1, Symb s2
       when s1 != s2 && is_constant s1 && is_constant s2 -> error t1 t2

  (*TODO try to factorize calls to
     instantiate/instantiable/nl_distinct_vars. *)
  | Meta(m,ts), _ when ts1 = [] && instantiate p c m ts t2 -> ()
  | _, Meta(m,ts) when ts2 = [] && instantiate p c m ts t1 -> ()

  | Meta(m,ts), Prod _ when ts1 = [] && instantiable c m ts h2 ->
      imitate_prod p c m h1 h2
  | Prod _, Meta(m,ts) when ts2 = [] && instantiable c m ts h1 ->
      imitate_prod p c m h1 h2

  | Meta(m,ts), _ when imitate_lam_cond h1 ts1
                      && nl_distinct_vars c ts <> None ->
      imitate_lam p c m; add_constr p (c,t1,t2)
  | _, Meta(m,ts) when imitate_lam_cond h2 ts2
                      && nl_distinct_vars c ts <> None ->
      imitate_lam p c m; add_constr p (c,t1,t2)

  | _ ->
  (* We normalize wrt user-defined rules and try again. *)
  if Logger.log_enabled () then log "whnf";
  let t1 = Eval.whnf c t1 and t2 = Eval.whnf c t2 in
  if Logger.log_enabled () then log (gre "solve %a") constr (c,t1,t2);
  let h1, ts1 = get_args t1 and h2, ts2 = get_args t2 in

  match h1, h2 with
  | Type, Type
  | Kind, Kind -> ()

  | Prod(a1,b1), Prod(a2,b2)
  | Abst(a1,b1), Abst(a2,b2) ->
      (* [ts1] and [ts2] must be empty because of typing or normalization. *)
      if Logger.log_enabled () then log "decompose";
      add_constr p (c,a1,a2);
      let (x,b1,b2) = unbind2 b1 b2 in
      let c' = (x,a1,None)::c in
      add_constr p (c',b1,b2)

  | Vari x1, Vari x2 when eq_vars x1 x2 ->
      if List.same_length ts1 ts2 then decompose p c ts1 ts2
      else error t1 t2

  | Type, (Kind|Prod _|Symb _|Vari _|Abst _)
  | Kind, (Type|Prod _|Symb _|Vari _|Abst _)
  | Prod _, (Type|Kind|Vari _|Abst _)
  | Vari _, (Type|Kind|Vari _|Prod _)
  | Abst _, (Type|Kind|Prod _)
    -> error t1 t2

  | ((Vari _|Abst _|Prod _), Symb s
    | Symb s, (Type|Kind|Vari _|Abst _|Prod _)) when s.sym_prop = Const ->
    error t1 t2

  | Symb s1, Symb s2 -> sym_sym_whnf p c t1 s1 ts1 t2 s2 ts2

  (*TODO try to factorize calls to
     instantiate/instantiable/nl_distinct_vars. *)
  | Meta(m,ts), _ when ts1 = [] && instantiate p c m ts t2 -> ()
  | _, Meta(m,ts) when ts2 = [] && instantiate p c m ts t1 -> ()

  | Meta(m,ts), Prod _ when ts1 = [] && instantiable c m ts h2 ->
      imitate_prod p c m h1 h2
  | Prod _, Meta(m,ts) when ts2 = [] && instantiable c m ts h1 ->
      imitate_prod p c m h1 h2

  | Meta(m,ts), _ when imitate_lam_cond h1 ts1
                      && nl_distinct_vars c ts <> None ->
      imitate_lam p c m; add_constr p (c,t1,t2)
  | _, Meta(m,ts) when imitate_lam_cond h2 ts2
                      && nl_distinct_vars c ts <> None ->
      imitate_lam p c m; add_constr p (c,t1,t2)

  | Meta(m,ts), Symb s ->
      if imitate_inj p c m ts ts1 s ts2
      then add_constr p (c,t1,t2)
      else add_to_unsolved p c t1 t2
  | Symb s, Meta(m,ts) ->
      if imitate_inj p c m ts ts2 s ts1
      then add_constr p (c,t1,t2)
      else add_to_unsolved p c t1 t2

  | Meta _, _
  | _, Meta _ -> add_to_unsolved p c t1 t2

  | Symb s, _ -> inverse p c t1 s ts1 t2
  | _, Symb s -> inverse p c t2 s ts2 t1

  | _ -> add_to_unsolved p c t1 t2
  done

(** [solve_noexn ~type_check p] tries to simplify the constraints of [p]. It
   returns [false] if it finds a constraint that cannot be
   satisfied. Otherwise, [p.to_solve] is empty but [p.unsolved] may still
   contain constraints that could not be simplified. Metavariable
   instantiations are type-checked only if the optional argument [~type_check]
   is [true] (default). *)
let solve_noexn : ?type_check:bool -> problem -> bool =
  fun ?(type_check=true) p ->
  Stdlib.(do_type_check := type_check);
  if Logger.log_enabled () then
    log_hndl (Color.blu "solve_noexn %a") problem p;
  try time_of "solve" (fun () -> solve p; true) with Unsolvable -> false

let solve_noexn =
  let open Stdlib in let r = ref false in fun ?type_check p ->
  Debug.(record_time Solving (fun () -> r := solve_noexn ?type_check p)); !r
