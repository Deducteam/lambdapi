(** Solving unification constraints. *)

open! Lplib
open Lplib.Extra

open Timed
open Common
open Error
open Term
open LibTerm
open Print
open Debug

(** Logging function for unification. *)
let logger_unif = new_logger 'u' "unif" "unification"
let log_unif = logger_unif.logger

(** [type_app a ts] returns [Some(u)] where [u] is a type of [add_args x ts]
   where [x] is any term of type [a] if [x] can be applied to at least
   [List.length ts] arguments, and [None] otherwise. *)
let rec type_app : ctxt -> term -> term list -> term option = fun ctx a ts ->
  match Eval.whnf ctx a, ts with
  | Prod(_,b), t::ts -> type_app ctx (Bindlib.subst b t) ts
  | _, [] -> Some a
  | _, _ -> None

(** Exception raised when a constraint is not solvable. *)
exception Unsolvable

(** [try_unif_rules ctx s t] tries to solve unification problem [ctx ⊢ s ≡ t]
   using declared unification rules. *)
let try_unif_rules : ctxt -> term -> term -> constr list option =
  fun ctx s t ->
  if !log_enabled then log_unif "check unif_rules";
  let exception No_match in
  let open Unif_rule in
  try
    let rhs =
      match Eval.tree_walk !(equiv.sym_tree) ctx [s;t] with
      | Some(r,[]) -> r
      | Some(_)    -> assert false (* Everything should be matched *)
      | None       ->
      match Eval.tree_walk !(equiv.sym_tree) ctx [t;s] with
      | Some(r,[]) -> r
      | Some(_)    -> assert false (* Everything should be matched *)
      | None       -> raise No_match
    in
    let cs = List.map (fun (t,u) -> (ctx,t,u)) (unpack rhs) in
    if !log_enabled then log_unif "rewrites to:%a" pp_constrs cs;
    Some cs
  with No_match ->
    if !log_enabled then log_unif "found no unif_rule";
    None

(** [instantiable ctx m ts u] tells whether, in a problem [m[ts]=u], [m] can
   be instantiated. It does not check whether the instantiation is closed
   though. *)
let instantiable : ctxt -> meta -> term array -> term -> bool =
  fun ctx m ts u -> not (Meta.occurs m u) && nl_distinct_vars ctx ts <> None

(** [instantiation ctx m ts u] tells whether, in a problem [m[ts]=u], [m] can
   be instantiated and returns the corresponding instantiation, simplified. It
   does not check whether the instantiation is closed though. *)
let instantiation : ctxt -> meta -> term array -> term ->
  tmbinder Bindlib.box option = fun ctx m ts u ->
  if not (Meta.occurs m u) then
    match nl_distinct_vars ctx ts with
    | None -> None
    | Some(vs, map) ->
        let u = Eval.simplify (sym_to_var map u) in
        Some (Bindlib.bind_mvar vs (lift u))
  else None

(** Checking type or not during meta instanciation. *)
let do_type_check = Stdlib.ref true

(** Initial set of constraints. *)
let initial : constr list Stdlib.ref = Stdlib.ref []

(** [is_initial c] checks whether [c] occurs in [!initial]. *)
let is_initial c = List.exists (LibTerm.eq_constr c) Stdlib.(!initial)

(** [instantiate ctx m ts u] check whether, in a problem [m[ts] ≡ u], [m] can
   be instantiated and, if so, instantiate it. *)
let instantiate : ctxt -> meta -> term array -> term -> bool =
  fun ctx m ts u ->
  if !log_enabled then log_unif "try instantiate";
  match instantiation ctx m ts u with
  | Some(bu) when Bindlib.is_closed bu ->
      let do_instantiate() =
        if !log_enabled then log_unif (red "%a ≔ %a") pp_meta m pp_term u;
        Meta.set m (Bindlib.unbox bu); true
      in
      if Stdlib.(!do_type_check) then
        begin
          let typ_mts =
            match type_app ctx !(m.meta_type) (Array.to_list ts) with
            | Some a -> a
            | None -> assert false
          in
          if !log_enabled then log_unif "check typing";
          match Infer.check_noexn [] ctx u typ_mts with
          | None ->
              if !log_enabled then log_unif "typing condition failed"; false
          | Some [] -> do_instantiate()
          | Some cs ->
              let cs = List.filter (fun c -> not (is_initial c)) cs in
              if cs = [] then do_instantiate()
              else
                (if !log_enabled then
                   log_unif
                     "failed because typing generated new constraints:%a"
                     pp_constrs cs;
                 false)
        end
      else do_instantiate()
  | i ->
      if !log_enabled then
        begin
          match i with
          | None ->
              if not (Meta.occurs m u) then log_unif "occur check failed"
              else log_unif "arguments are not distinct variables: %a"
                     (Array.pp pp_term " ") ts
          | Some _ -> log_unif "not closed"
        end;
      false

(** [error t1 t2]
@raise Unsolvable. *)
let error : term -> term -> 'a = fun t1 t2 ->
  fatal_msg "\n[%a]\nand\n[%a]\nare not convertible.\n" pp_term t1 pp_term t2;
  raise Unsolvable

(** [add_constr c cs] adds [c] to [!initial] and returns [c::cs]. *)
let add_constr : constr -> constr list -> constr list = fun c cs ->
  if !log_enabled then log_unif (mag "%a") pp_constr c;
  Stdlib.(initial := c::!initial);
  c::cs

let add_constr_fold cs c = add_constr c cs

(** [add_unif_rule_constr cs (ctx,t,u)] adds to [cs] the constraint
   [(ctx,t,u)] as well as the constraint [(ctx,a,b)] where [a] is the type of
   [t] and [b] the type of [u] if they can be infered. *)
let add_unif_rule_constr : constr list -> constr -> constr list =
  fun cs ((ctx,t,u) as c) ->
  match Infer.infer_noexn [] ctx t with
  | None ->
      begin
        match Infer.infer_noexn [] ctx u with
        | None -> add_constr c cs
        | Some (_,csu) ->
            List.fold_left add_constr_fold (add_constr c cs) csu
      end
  | Some (a,cst) ->
      match Infer.infer_noexn cst ctx u with
      | None -> List.fold_left add_constr_fold (add_constr c cs) cst
      | Some (b,cstu) ->
          let cs = List.fold_left add_constr_fold (add_constr c cs) cstu in
          if Eval.eq_modulo ctx a b then cs else add_constr (ctx,a,b) cs

(** [add_to_unsolved t1 t2 p] checks whether [t1] is equivalent to [t2]. If
   not, then it tries to apply unification rules on the problem [t1 ≡ t2]. If
   no unification rule applies then it adds [t1 = t2] in the unsolved problems
   of [p]. *)
let add_to_unsolved : ctxt -> term -> term -> problem -> problem =
  fun ctx t1 t2 p ->
  if Eval.eq_modulo ctx t1 t2 then
    (if !log_enabled then log_unif "equivalent terms"; p)
  else match try_unif_rules ctx t1 t2 with
  | None ->
      if !log_enabled then log_unif "move to unsolved";
      {p with unsolved = (ctx,t1,t2) :: p.unsolved}
  | Some([]) -> assert false
  (* Unification rules generate non empty list of unification constraints *)
  | Some(cs) ->
      {p with to_solve = List.fold_left add_unif_rule_constr p.to_solve cs}

(** [decompose ctx ts1 ts2] tries to decompose a problem of the form [h ts1 ≡
   h ts2] into the problems [t1 ≡ u1; ..; tn ≡ un], assuming that [ts1 =
   [t1;..;tn]] and [ts2 = [u1;..;un]]. *)
let decompose : ctxt -> term list -> term list -> problem -> problem =
  fun ctx ts1 ts2 p ->
    if !log_enabled && ts1 <> [] then log_unif "decompose";
    let add_arg_constr a b cs = add_constr (ctx,a,b) cs in
    (* we use fold_right2 instead of fold_left2 to keep the order of the
       decomposition: f a b ≡ f a' b' => a ≡ a && b ≡ b' *)
    {p with to_solve = List.fold_right2 add_arg_constr ts1 ts2 p.to_solve}

(** [add_constr c p] adds [c] into [!initial] and [p]. *)
let add_constr : constr -> problem -> problem = fun c p ->
  {p with to_solve = c::p.to_solve}

(** For a problem [m[vs] ≡ s(ts)] in context [ctx], where [vs] are distinct
   variables, [m] is a meta of type [Πy0:a0,..,Πyk-1:ak-1,b] with [k = length
   vs], [s] is an injective symbol of type [Πx0:b0,..,Πxn-1:bn-1,c] with [n =
   length ts], [imitate_inj ctx m vs us s ts] tries to instantiate [m] by
   [s(m0[vs],..,mn-1[vs])] where [mi] is a fresh meta of type
   [Πv0:a0,..,Πvk-1:ak-1{y0=v0,..,yk-2=vk-2}, bi{x0=m0[vs],..,xi-1=mi-1[vs]}]
   and returns [true], and returns [false] if it cannot. *)
let imitate_inj :
      ctxt -> meta -> term array -> term list -> sym -> term list -> bool =
  fun ctx m vs us s ts ->
  if !log_enabled then
    log_unif "imitate_inj %a ≡ %a" pp_term (add_args (Meta(m,vs)) us)
                                   pp_term (add_args (Symb s) ts);
  let exception Cannot_imitate in
  try
    if not (us = [] && is_injective s) then raise Cannot_imitate;
    let vars =
      match distinct_vars ctx vs with
      | None -> raise Cannot_imitate
      | Some vars -> vars
    in
    (* Build the environment (yk-1,ak-1{y0=v0,..,yk-2=vk-2});..;(y0,a0). *)
    let env, _ = Env.of_prod_using ctx vars !(m.meta_type) in
    (* Build the term s(m0[vs],..,mn-1[vs]). *)
    let k = Array.length vars in
    let t =
      let rec build i acc t =
        if i <= 0 then add_args (Symb s) (List.rev acc) else
        match unfold t with
        | Prod(a,b) ->
            let m = Meta.fresh (Env.to_prod env (lift a)) k in
            let u = Meta (m,vs) in
            build (i-1) (u::acc) (Bindlib.subst b u)
        | _ -> raise Cannot_imitate
      in build (List.length ts) [] !(s.sym_type)
    in
    Meta.set m (Bindlib.unbox (Bindlib.bind_mvar vars (lift t))); true
  with Cannot_imitate -> false

(** [imitate_lam_cond h ts] tells whether [ts] is headed by a variable not
   occurring in [h]. *)
let imitate_lam_cond : term -> term list -> bool = fun h ts ->
  match ts with
  | [] -> false
  | e :: _ ->
      match unfold e with
      | Vari x -> not (Bindlib.occur x (lift h))
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
let imitate_lam : ctxt -> meta -> problem -> problem = fun ctx m p ->
    if !log_enabled then log_unif "imitate_lam %a" pp_meta m;
    let n = m.meta_arity in
    let (env, t) = Env.of_prod_nth ctx n !(m.meta_type) in
    let x,a,env',b,p =
      match Eval.whnf ctx t with
      | Prod(a,b) ->
         let x,b = Bindlib.unbind b in
         let a = lift a in
         let env' = Env.add x a None env in
         x,a,env',lift b,p
      | _ ->
         (* After type inference, a similar constraint should have already
            been generated but has not been processed yet. *)
         let tm2 = Env.to_prod env _Type in
         let m2 = Meta.fresh tm2 n in
         let a = _Meta m2 (Env.to_tbox env) in
         let x = new_tvar "x" in
         let env' = Env.add x a None env in
         let tm3 = Env.to_prod env' _Type in
         let m3 = Meta.fresh tm3 (n+1) in
         let b = _Meta m3 (Env.to_tbox env') in
         (* Could be optimized by extending [Env.to_tbox env]. *)
         let u = Bindlib.unbox (_Prod a (Bindlib.bind_var x b)) in
         x,a,env',b,add_constr (Env.to_ctxt env,u,t) p
    in
    let tm1 = Env.to_prod env' b in
    let m1 = Meta.fresh tm1 (n+1) in
    let u1 = _Meta m1 (Env.to_tbox env') in
    let xu1 = _Abst a (Bindlib.bind_var x u1) in
    let v = Bindlib.bind_mvar (Env.vars env) xu1 in
    Meta.set m (Bindlib.unbox v); p

(** [inverse_opt s ts v] returns [Some(t, inverse s v)] if [ts=[t]], [s] is
   injective and [inverse s v] does not fail, and [None] otherwise. *)
let inverse_opt : sym -> term list -> term -> (term * term) option =
  fun s ts v ->
  if !log_enabled then log_unif "try inverse";
  try
    match ts with
    | [t] when is_injective s -> Some (t, Inverse.inverse s v)
    | _ -> raise Not_found
  with Not_found -> if !log_enabled then log_unif "failed"; None

(** [add_inverse t1 s ts1 t2] tries to replace a problem of the form [t1 ≡ t2]
   with [t1 = s(ts1)] and [ts1=[u]] by [u ≡ inverse s t2], when [s] is
   injective. *)
let add_inverse :
      ctxt -> term -> sym -> term list -> term -> problem -> problem =
  fun ctx t1 s ts1 t2 p ->
  match inverse_opt s ts1 t2 with
  | Some (t, u) -> add_constr (ctx,t,u) p
  | _ -> add_to_unsolved ctx t1 t2 p

(** For a problem of the form [h1 ≡ h2] with [h1 = m[ts]], [h2 = Πx:_,_] (or
   the opposite) and [ts] distinct bound variables, [imitate_prod m h1 h2 p]
   instantiate [m] to a product and add the problem [h1 ≡ h2] to [p]. *)
let imitate_prod : ctxt -> meta -> term -> term -> problem -> problem =
  fun ctx m h1 h2 p ->
  if !log_enabled then log_unif "imitate_prod %a" pp_meta m;
  Infer.set_to_prod m; add_constr (ctx,h1,h2) p

(** [sym_sym_whnf ctx t1 s1 ts1 t2 s2 ts2 p] handles the case [s1(ts1) =
   s2(ts2); p] when [s1(ts1)] and [s2(ts2)] are in whnf. *)
let sym_sym_whnf :
      ctxt -> term -> sym -> term list -> term -> sym -> term list -> problem
      -> problem =
  fun ctx t1 s1 ts1 t2 s2 ts2 p ->
  if s1 == s2 then
    match s1.sym_prop with
    | (Const|Injec) ->
        if List.same_length ts1 ts2 then decompose ctx ts1 ts2 p
        else error t1 t2
    | _ -> add_to_unsolved ctx t1 t2 p
  else
    match s1.sym_prop, s2.sym_prop with
    | Const, Const -> error t1 t2
    | _, _ ->
        match inverse_opt s1 ts1 t2 with
        | Some (t, u) -> add_constr (ctx,t,u) p
        | None -> add_inverse ctx t2 s2 ts2 t1 p

(** [solve p] tries to solve the unification problem [p] and
    returns the constraints that could not be solved. *)
let rec solve : problem -> constr list = fun p ->
  match p with
  | {to_solve = []; unsolved = []; _} -> []
  | {to_solve = []; unsolved = cs; recompute = true} ->
      if !log_enabled then log_unif "recompute";
      solve {empty_problem with to_solve = cs}
  | {to_solve = []; unsolved = cs; _} -> cs
  | {to_solve = (ctx,t1,t2)::to_solve; _} ->

  (* We remove the first constraint from [p] for not looping. *)
  let p = {p with to_solve} in

  (* We take the beta-whnf. *)
  let t1 = Eval.whnf_beta t1 and t2 = Eval.whnf_beta t2 in
  if !log_enabled then log_unif (gre "%a") pp_constr (ctx,t1,t2);
  let (h1, ts1) = LibTerm.get_args t1
  and (h2, ts2) = LibTerm.get_args t2 in

  match h1, h2 with
  | Type, Type
  | Kind, Kind -> solve p

  | Prod(a1,b1), Prod(a2,b2)
  | Abst(a1,b1), Abst(a2,b2) ->
      if !log_enabled then log_unif "decompose";
      let (x,b1,b2) = Bindlib.unbind2 b1 b2 in
      let ctx' = (x,a1,None)::ctx in
      (* [ts1] and [ts2] must be empty because of typing or normalization. *)
      solve (add_constr (ctx,a1,a2) (add_constr (ctx',b1,b2) p))

  | Vari x1, Vari x2 when Bindlib.eq_vars x1 x2 ->
      if List.same_length ts1 ts2 then solve (decompose ctx ts1 ts2 p)
      else error t1 t2

  | Type, (Kind|Prod _|Symb _|Vari _|Abst _)
  | Kind, (Type|Prod _|Symb _|Vari _|Abst _)
  | Prod _, (Type|Kind|Vari _)
  | Vari _, (Type|Kind|Vari _|Prod _)
    -> error t1 t2

  | Symb s1, Symb s2
       when s1 == s2 && s1.sym_prop <> Defin && List.same_length ts1 ts2 ->
      solve (decompose ctx ts1 ts2 p)
  | Symb s1, Symb s2
       when s1 != s2 && s1.sym_prop = Const && s2.sym_prop = Const ->
      error t1 t2

  | Meta(m,ts), _ when ts1 = [] && instantiate ctx m ts t2 ->
     solve {p with recompute = true}
  | _, Meta(m,ts) when ts2 = [] && instantiate ctx m ts t1 ->
     solve {p with recompute = true}

  | Meta(m,ts), Prod _ when ts1 = [] && instantiable ctx m ts h2 ->
      solve (imitate_prod ctx m h1 h2 p)
  | Prod _, Meta(m,ts) when ts2 = [] && instantiable ctx m ts h1 ->
      solve (imitate_prod ctx m h1 h2 p)

  | Meta(m,_), _ when imitate_lam_cond h1 ts1 ->
      let p = imitate_lam ctx m p in solve (add_constr (ctx,t1,t2) p)
  | _, Meta(m,_) when imitate_lam_cond h2 ts2 ->
      let p = imitate_lam ctx m p in solve (add_constr (ctx,t1,t2) p)

  | _ ->

  (* We reduce [t1] and [t2] and try again. *)
  let t1 = Eval.whnf ctx t1 and t2 = Eval.whnf ctx t2 in
  let (h1, ts1) = LibTerm.get_args t1
  and (h2, ts2) = LibTerm.get_args t2 in

  if !log_enabled then log_unif "normalize";
  if !log_enabled then log_unif (gre "%a") pp_constr (ctx,t1,t2);

  match h1, h2 with
  | Type, Type
  | Kind, Kind -> solve p

  | Prod(a1,b1), Prod(a2,b2)
  | Abst(a1,b1), Abst(a2,b2) ->
      if !log_enabled then log_unif "decompose";
      let (x,b1,b2) = Bindlib.unbind2 b1 b2 in
      let ctx' = (x,a1,None)::ctx in
      (* [ts1] and [ts2] must be empty because of typing or normalization. *)
      solve (add_constr (ctx,a1,a2) (add_constr (ctx',b1,b2) p))

  | Vari x1, Vari x2 when Bindlib.eq_vars x1 x2 ->
      if List.same_length ts1 ts2 then solve (decompose ctx ts1 ts2 p)
      else error t1 t2

  | Type, (Kind|Prod _|Symb _|Vari _|Abst _)
  | Kind, (Type|Prod _|Symb _|Vari _|Abst _)
  | Prod _, (Type|Kind|Vari _|Abst _)
  | Vari _, (Type|Kind|Vari _|Prod _)
  | Abst _, (Type|Kind|Prod _)
    -> error t1 t2

  | Symb s1, Symb s2 -> solve (sym_sym_whnf ctx t1 s1 ts1 t2 s2 ts2 p)

  | Meta(m,ts), _ when ts1 = [] && instantiate ctx m ts t2 ->
     solve {p with recompute = true}
  | _, Meta(m,ts) when ts2 = [] && instantiate ctx m ts t1 ->
     solve {p with recompute = true}

  | Meta(m,ts), Prod _ when ts1 = [] && instantiable ctx m ts h2 ->
      solve (imitate_prod ctx m h1 h2 p)
  | Prod _, Meta (m,ts) when ts2 = [] && instantiable ctx m ts h1 ->
      solve (imitate_prod ctx m h1 h2 p)

  | Meta(m,_), _ when imitate_lam_cond h1 ts1 ->
      let p = imitate_lam ctx m p in solve (add_constr (ctx,t1,t2) p)
  | _, Meta(m,_) when imitate_lam_cond h2 ts2 ->
      let p = imitate_lam ctx m p in solve (add_constr (ctx,t1,t2) p)

  | Meta(m,ts), Symb s ->
      if imitate_inj ctx m ts ts1 s ts2 then solve (add_constr (ctx,t1,t2) p)
      else solve (add_to_unsolved ctx t1 t2 p)
  | Symb s, Meta(m,ts) ->
      if imitate_inj ctx m ts ts2 s ts1 then solve (add_constr (ctx,t1,t2) p)
      else solve (add_to_unsolved ctx t1 t2 p)

  | Meta _, _
  | _, Meta _ -> solve (add_to_unsolved ctx t1 t2 p)

  | Symb s, _ -> solve (add_inverse ctx t1 s ts1 t2 p)
  | _, Symb s -> solve (add_inverse ctx t2 s ts2 t1 p)

  | _ -> solve (add_to_unsolved ctx t1 t2 p)

(** [solve p] tries to solve the unification problem [p] and
    returns the constraints that could not be solved.
    This is the entry point setting the flag type_check *)
let solve : ?type_check:bool -> problem -> constr list =
  fun ?(type_check=true) p ->
  if !log_enabled then log_hndl "solve %a" pp_problem p;
  Stdlib.(do_type_check := type_check; initial := p.to_solve);
  time_of (fun () -> solve p)

(** [solve_noexn problem] attempts to solve [problem]. If there is
   no solution, the value [None] is returned. Otherwise [Some(cs)] is
   returned, where the list [cs] is a list of unsolved convertibility
   constraints. *)
let solve_noexn : ?type_check:bool -> problem -> constr list option =
  fun ?(type_check=true) p ->
  try Some (solve ~type_check p) with Unsolvable -> None

(** [eq_noexn c t u] tries to unify the terms [t] and [u] in context [c], by
   instantiating their metavariables. *)
let eq_noexn : ?type_check:bool -> ctxt -> term -> term -> bool =
  fun ?(type_check=true) c t u ->
  solve_noexn ~type_check {empty_problem with to_solve=[c,t,u]} = Some []
