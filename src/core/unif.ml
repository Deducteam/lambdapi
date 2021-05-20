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

(** [type_app c a ts] returns [Some u] where [u] is a type of [add_args x ts]
   in context [c] where [x] is any term of type [a] if [x] can be applied to
   at least [List.length ts] arguments, and [None] otherwise. *)
let rec type_app : ctxt -> term -> term list -> term option = fun c a ts ->
  match Eval.whnf c a, ts with
  | Prod(_,b), t::ts -> type_app c (Bindlib.subst b t) ts
  | _, [] -> Some a
  | _, _ -> None

(** [add_constr p c] adds the constraint [c] into [p.to_solve]. *)
let add_constr : problem -> constr -> unit = fun p c ->
  if !log_enabled then log_unif (mag "add %a") pp_constr c;
  p.to_solve <- c::p.to_solve

(** [add_unif_rule_constr p (c,t,u)] adds to [p] the constraint [(c,t,u)]
   as well as the constraint [(c,a,b)] where [a] is the type of [t] and [b]
   the type of [u] if they can be infered. *)
let add_unif_rule_constr : problem -> constr -> unit = fun p (c,t,u) ->
  match Infer.infer_noexn p c t with
  | None -> ignore (Infer.infer_noexn p c u)
  | Some a ->
      match Infer.infer_noexn p c u with
      | Some b when not (Eval.eq_modulo c a b) -> add_constr p (c,a,b)
      | _ -> ()

(** [try_unif_rules p c s t] tries to simplify the unification problem [c
   ⊢ s ≡ t] with the user-defined unification rules. *)
let try_unif_rules : problem -> ctxt -> term -> term -> bool =
  fun p c s t ->
  if !log_enabled then log_unif "check unif_rules";
  let exception No_match in
  let open Unif_rule in
  try
    let rhs =
      match Eval.tree_walk p !(equiv.sym_dtree) c [s;t] with
      | Some(r,[]) -> r
      | Some(_)    -> assert false (* Everything should be matched *)
      | None       ->
      match Eval.tree_walk p !(equiv.sym_dtree) c [t;s] with
      | Some(r,[]) -> r
      | Some(_)    -> assert false (* Everything should be matched *)
      | None       -> raise No_match
    in
    let cs = List.map (fun (t,u) -> (c,t,u)) (unpack rhs) in
    if !log_enabled then log_unif "rewrites to:%a" pp_constrs cs;
    List.iter (add_unif_rule_constr p) cs;
    true
  with No_match ->
    if !log_enabled then log_unif "found no unif_rule";
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
      ctxt -> meta -> term array -> term -> tmbinder Bindlib.box option =
  fun c m ts u ->
  match nl_distinct_vars c ts with
    | None -> None
    | Some(vs, map) ->
        if LibMeta.occurs m c u then None else
        let u = Eval.simplify (sym_to_var map u) in
        Some (Bindlib.bind_mvar vs (lift u))

(** Checking type or not during meta instanciation. *)
let do_type_check = Stdlib.ref true

(** [instantiate p c m ts u] checks whether, with a constraint [m[ts] ≡ u],
   [m] can be instantiated and, if so, instantiates it and updates the
   metavariables of [p]. *)
let instantiate : problem -> ctxt -> meta -> term array -> term -> bool =
  fun p c m ts u ->
  if !log_enabled then log_unif "try instantiate";
  match instantiation c m ts u with
  | Some b when Bindlib.is_closed b ->
      let do_instantiate() =
        if !log_enabled then log_unif (red "%a ≔ %a") pp_meta m pp_term u;
        LibMeta.set p m (Bindlib.unbox b); p.recompute <- true; true
      in
      if Stdlib.(!do_type_check) then
        begin
          if !log_enabled then log_unif "check typing";
          let typ_mts =
            match type_app c !(m.meta_type) (Array.to_list ts) with
            | Some a -> a
            | None -> assert false
          in
          if Infer.check_noexn p c u typ_mts then do_instantiate()
          else (if !log_enabled then log_unif "typing failed"; false)
        end
      else do_instantiate()
  | i ->
      if !log_enabled then
        begin
          match i with
          | None ->
              if not (LibMeta.occurs m c u) then log_unif "occur check failed"
              else log_unif "arguments are not distinct variables: %a"
                     (Array.pp pp_term " ") ts
          | Some _ -> log_unif "not closed"
        end;
      false

(** [add_to_unsolved p c t1 t2] checks whether [t1] is equivalent to [t2] in
   context [c]. If not, then it tries to apply unification rules. If no
   unification rule applies then it adds [(c,t1,t2)] to the unsolved
   constraints of [p]. *)
let add_to_unsolved : problem -> ctxt -> term -> term -> unit =
  fun p c t1 t2 ->
  if Eval.eq_modulo c t1 t2 then
    (if !log_enabled then log_unif "equivalent terms")
  else if not (try_unif_rules p c t1 t2) then
    (if !log_enabled then log_unif "move to unsolved";
     p.unsolved <- (c,t1,t2) :: p.unsolved)

(** [decompose p c ts1 ts2] tries to decompose a problem of the form [h ts1 ≡
   h ts2] into the problems [t1 ≡ u1; ..; tn ≡ un], assuming that [ts1 =
   [t1;..;tn]] and [ts2 = [u1;..;un]]. *)
let decompose : problem -> ctxt -> term list -> term list -> unit =
  fun p c ts1 ts2 ->
    if !log_enabled && ts1 <> [] then log_unif "decompose";
    List.iter2 (fun a b -> add_constr p (c,a,b)) ts1 ts2

(** For a problem of the form [h1 ≡ h2] with [h1 = m[ts]], [h2 = Πx:_,_] (or
   the opposite) and [ts] distinct bound variables, [imitate_prod m h1 h2 p]
   instantiates [m] to a product and adds the constraint [h1 ≡ h2] to [p]. *)
let imitate_prod : problem -> ctxt -> meta -> term -> term -> unit =
  fun p c m h1 h2 ->
  if !log_enabled then log_unif "imitate_prod %a" pp_meta m;
  Infer.set_to_prod p m; add_constr p (c,h1,h2)

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
  if !log_enabled then
    log_unif "imitate_inj %a ≡ %a" pp_term (add_args (mk_Meta(m,vs)) us)
                                   pp_term (add_args (mk_Symb s) ts);
  let exception Cannot_imitate in
  try
    if not (us = [] && is_injective s) then raise Cannot_imitate;
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
            let m = LibMeta.fresh p (Env.to_prod env (lift a)) k in
            let u = mk_Meta (m,vs) in
            build (i-1) (u::acc) (Bindlib.subst b u)
        | _ -> raise Cannot_imitate
      in build (List.length ts) [] !(s.sym_type)
    in
    if !log_enabled then log_unif (red "%a ≔ %a") pp_meta m pp_term t;
    LibMeta.set p m (Bindlib.unbox (Bindlib.bind_mvar vars (lift t))); true
  with Cannot_imitate | Invalid_argument _ -> false

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
let imitate_lam : problem -> ctxt -> meta -> unit = fun p c m ->
    if !log_enabled then log_unif "imitate_lam %a" pp_meta m;
    let n = m.meta_arity in
    let env, t = Env.of_prod_nth c n !(m.meta_type) in
    let of_prod a b =
      let x,b = LibTerm.unbind_name "x" b in
      let a = lift a in
      let env' = Env.add x a None env in
      x, a, env', lift b
    in
    let x, a, env', b =
      match Eval.whnf c t with
      | Prod(a,b) -> of_prod a b
      | Meta(n,ts) as t when nl_distinct_vars c ts <> None ->
          begin
            Infer.set_to_prod p n;
            match unfold t with
            | Prod(a,b) -> of_prod a b
            | _ -> assert false
          end
      | _ ->
         let tm2 = Env.to_prod env _Type in
         let m2 = LibMeta.fresh p tm2 n in
         let a = _Meta m2 (Env.to_tbox env) in
         let x = new_tvar "x" in
         let env' = Env.add x a None env in
         let tm3 = Env.to_prod env' _Type in
         let m3 = LibMeta.fresh p tm3 (n+1) in
         let b = _Meta m3 (Env.to_tbox env') in
         let u = Bindlib.unbox (_Prod a (Bindlib.bind_var x b)) in
         add_constr p (Env.to_ctxt env, u, t);
         x, a, env', b
    in
    let tm1 = Env.to_prod env' b in
    let m1 = LibMeta.fresh p tm1 (n+1) in
    let u1 = _Meta m1 (Env.to_tbox env') in
    let xu1 = _Abst a (Bindlib.bind_var x u1) in
    let v = Bindlib.bind_mvar (Env.vars env) xu1 in
    if !log_enabled then
      log_unif (red "%a ≔ %a") pp_meta m pp_term (Bindlib.unbox xu1);
    LibMeta.set p m (Bindlib.unbox v)

(** [inverse_opt s ts v] returns [Some(t, inverse s v)] if [ts=[t]], [s] is
   injective and [inverse s v] does not fail, and [None] otherwise. *)
let inverse_opt : sym -> term list -> term -> (term * term) option =
  fun s ts v ->
  if !log_enabled then log_unif "try inverse %a" pp_sym s;
  try
    match ts with
    | [t] when is_injective s -> Some (t, Inverse.inverse s v)
    | _ -> raise Not_found
  with Not_found -> if !log_enabled then log_unif "failed"; None

(** Exception raised when a constraint is not solvable. *)
exception Unsolvable

(** [error t1 t2]
@raise Unsolvable. *)
let error : term -> term -> 'a = fun t1 t2 ->
  fatal_msg "\n[%a]\nand\n[%a]\nare not convertible.\n" pp_term t1 pp_term t2;
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
            if !log_enabled then log_unif "move to unsolved";
            p.unsolved <- (c,t1,t2) :: p.unsolved

(** [sym_sym_whnf p c t1 s1 ts1 t2 s2 ts2 p] handles the case [s1(ts1) =
   s2(ts2); p] when [s1(ts1)] and [s2(ts2)] are in whnf. *)
let sym_sym_whnf :
      problem -> ctxt -> term -> sym -> term list -> term -> sym -> term list
      -> unit =
  fun p c t1 s1 ts1 t2 s2 ts2 ->
  if s1 == s2 then
    match s1.sym_prop with
    | (Const|Injec) ->
        if List.same_length ts1 ts2 then decompose p c ts1 ts2
        else error t1 t2
    | _ -> add_to_unsolved p c t1 t2
  else
    match s1.sym_prop, s2.sym_prop with
    | Const, Const -> error t1 t2
    | _, _ ->
        match inverse_opt s1 ts1 t2 with
        | Some (t, u) -> add_constr p (c,t,u)
        | None -> inverse p c t2 s2 ts2 t1

(** [solve_noexn p] tries to simplify the constraints of [p].
@raise [Unsolvable] if it finds a constraint that cannot be satisfied.
Otherwise, [p.to_solve] is empty but [p.unsolved] may still contain
constraints that could not be simplified. *)
let solve : problem -> unit = fun p ->
  while p.to_solve <> [] || (p.recompute && p.unsolved <> []) do
  match p.to_solve with
  | [] ->
      if !log_enabled then log_unif "recompute";
      p.to_solve <- p.unsolved;
      p.unsolved <- [];
      p.recompute <- false
  | (c,t1,t2)::to_solve ->
  (*if !log_enabled then
    log_unif "%d constraints" (1 + List.length to_solve);*)

  (* We remove the first constraint from [p] for not looping. *)
  p.to_solve <- to_solve;

  (* We take the beta-whnf. *)
  let t1 = Eval.whnf_beta t1 and t2 = Eval.whnf_beta t2 in
  if !log_enabled then log_unif (gre "solve %a") pp_constr (c,t1,t2);
  let (h1, ts1) = get_args t1
  and (h2, ts2) = get_args t2 in

  match h1, h2 with
  | Type, Type
  | Kind, Kind -> ()

  | Prod(a1,b1), Prod(a2,b2)
  | Abst(a1,b1), Abst(a2,b2) ->
      (* [ts1] and [ts2] must be empty because of typing or normalization. *)
      if !log_enabled then log_unif "decompose";
      let (x,b1,b2) = Bindlib.unbind2 b1 b2 in
      let c' = (x,a1,None)::c in
      add_constr p (c',b1,b2);
      add_constr p (c,a1,a2)

  | Vari x1, Vari x2 when Bindlib.eq_vars x1 x2 ->
      if List.same_length ts1 ts2 then decompose p c ts1 ts2
      else error t1 t2

  | Type, (Kind|Prod _|Symb _|Vari _|Abst _)
  | Kind, (Type|Prod _|Symb _|Vari _|Abst _)
  | Prod _, (Type|Kind|Vari _)
  | Vari _, (Type|Kind|Vari _|Prod _)
    -> error t1 t2

  | Symb s1, Symb s2
       when s1 == s2 && s1.sym_prop <> Defin && List.same_length ts1 ts2 ->
      decompose p c ts1 ts2
  | Symb s1, Symb s2
       when s1 != s2 && s1.sym_prop = Const && s2.sym_prop = Const ->
      error t1 t2

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

  (* We reduce [t1] and [t2] and try again. *)
  let t1 = Eval.whnf c t1 and t2 = Eval.whnf c t2 in
  let (h1, ts1) = get_args t1
  and (h2, ts2) = get_args t2 in

  if !log_enabled then log_unif "normalize";
  if !log_enabled then log_unif (gre "solve %a") pp_constr (c,t1,t2);

  match h1, h2 with
  | Type, Type
  | Kind, Kind -> ()

  | Prod(a1,b1), Prod(a2,b2)
  | Abst(a1,b1), Abst(a2,b2) ->
      (* [ts1] and [ts2] must be empty because of typing or normalization. *)
      if !log_enabled then log_unif "decompose";
      add_constr p (c,a1,a2);
      let (x,b1,b2) = Bindlib.unbind2 b1 b2 in
      let c' = (x,a1,None)::c in
      add_constr p (c',b1,b2)

  | Vari x1, Vari x2 when Bindlib.eq_vars x1 x2 ->
      if List.same_length ts1 ts2 then decompose p c ts1 ts2
      else error t1 t2

  | Type, (Kind|Prod _|Symb _|Vari _|Abst _)
  | Kind, (Type|Prod _|Symb _|Vari _|Abst _)
  | Prod _, (Type|Kind|Vari _|Abst _)
  | Vari _, (Type|Kind|Vari _|Prod _)
  | Abst _, (Type|Kind|Prod _)
    -> error t1 t2

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
  if !log_enabled then log_hndl "solve %a" pp_problem p;
  Stdlib.(do_type_check := type_check);
  try time_of (fun () -> solve p; true) with Unsolvable -> false
