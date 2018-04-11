(** Type-checking and inference. *)

open Console
open Terms
open Print
open Eval

(** [subst_from_constrs cs] builds a //typing substitution// from the list  of
    constraints [cs]. The returned substitution is given by a couple of arrays
    [(xs,ts)] of the same length.  The array [xs] contains the variables to be
    substituted using the terms of [ts] at the same index. *)
let subst_from_constrs : problem list -> tvar array * term array = fun cs ->
  let rec build_sub acc cs =
    match cs with
    | []        -> acc
    | (c,a,b)::cs ->
        let (ha,argsa) = get_args a in
        let (hb,argsb) = get_args b in
        match (unfold ha, unfold hb) with
        | (Symb(sa), Symb(sb))
            when sa == sb && not sa.sym_definable && not sb.sym_definable ->
            let cs =
              try List.fold_left2 (fun l t1 t2 -> (c,t1,t2)::l) cs argsa argsb
              with Invalid_argument _ -> cs
            in
            build_sub acc cs
        | (Vari(x)      , _            ) when argsa = [] ->
            build_sub ((x,b)::acc) cs
        | (_            , Vari(x)      ) when argsb = [] ->
            build_sub ((x,a)::acc) cs
        | (a            , b            ) ->
            wrn "Not implemented [%a] [%a]...\n%!" pp a pp b;
            build_sub acc cs
  in
  let sub = build_sub [] cs in
  (Array.of_list (List.map fst sub), Array.of_list (List.map snd sub))

(** [eq_modulo_constrs cs t u] checks  whether the terms [t] and [u] are equal
    modulo rewriting and a list of (valid) constraints [cs]. *)
let eq_modulo_constrs : problem list -> term -> term -> bool
  = fun constrs a b ->
  if !debug_sr then log "sr" "%a == %a (with constraints)" pp a pp b;
  let (xs,sub) = subst_from_constrs constrs in
  let p = Bindlib.box_pair (lift a) (lift b) in
  let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
  let (a,b) = Bindlib.msubst p sub in
  if !debug_sr then log "sr" "%a == %a (after substitution)" pp a pp b;
  eq_modulo a b

(** [check_rule r] check whether rule [r] is well-typed. The program
    fails gracefully in case of error. *)
let check_rule : rspec -> unit = fun spec ->
  let {rspec_symbol = s; rspec_ty_map = ty_map; rspec_rule = rule} = spec in
  if !debug_sr then log "sr" "Typing the rule [%a]" pp_rule (s, rule);
  (** We process the LHS to replace pattern variables by metavariables. *)
  let arity = Bindlib.mbinder_arity rule.rhs in
  let metas = Array.init arity (fun _ -> None) in
  let rec to_m : term -> tbox = fun t ->
    let to_m_binder b x = to_m (Bindlib.subst b (mkfree x)) in
    match unfold t with
    | Vari(x)     -> _Vari x
    | Symb(s)     -> _Symb s
    | Abst(a,t)   -> _Abst (lift a) (Bindlib.binder_name t) (to_m_binder t)
    | Appl(t,u)   -> _Appl (to_m t) (to_m u)
    | Patt(i,n,m) ->
        begin
          let m = Array.map to_m m in
          let l = Array.length m in
          match i with
          | None    -> _Meta (new_meta (List.assoc n ty_map) l) m
          | Some(i) ->
              match metas.(i) with
              | Some(v) -> _Meta v m
              | None    ->
                  let v = new_meta (List.assoc n ty_map) l in
                  metas.(i) <- Some(v);
                  _Meta v m
        end
    | Type        -> assert false (* Cannot appear in LHS. *)
    | Kind        -> assert false (* Cannot appear in LHS. *)
    | Prod(a,b)   -> assert false (* Cannot appear in LHS. *)
    | Meta(r,m)   -> assert false (* Cannot appear in LHS. *)
    | TEnv(t,m)   -> assert false (* Cannot appear in LHS. *)
  in
  let lhs = List.map (fun p -> Bindlib.unbox (to_m p)) rule.lhs in
  let lhs = add_args (Symb(s)) lhs in
  (** We substitute the RHS with the corresponding metavariables.*)
  let fn m =
    let m = match m with Some(m) -> m | None -> assert false in
    let names = Array.init m.meta_arity (Printf.sprintf "x%i") in
    TE_Some(Bindlib.mbinder_from_fun names (fun e -> Meta(m,e)))
  in
  let te_envs = Array.map fn metas in
  let rhs = Bindlib.msubst rule.rhs te_envs in
  (* Infer the type of the LHS and the constraints. *)
  let (lhs_constrs, ty_lhs) =
    Infer2.with_constraints (Infer2.raw_infer empty_ctxt) lhs in
  (* Infer the type of the RHS and the constraints. *)
  let (rhs_constrs, ty_rhs) =
    Infer2.with_constraints (Infer2.raw_infer empty_ctxt) rhs in
  (* Checking the implication of constraints. *)
  let check_constraint (_,a,b) =
    if not (eq_modulo_constrs lhs_constrs a b) then
      fatal "A constraint is not satisfied...\n"
  in
  List.iter check_constraint rhs_constrs
