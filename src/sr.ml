(** Type-checking and inference. *)

open Console
open Terms
open Print
open Eval
open Unif
open Typing

(** [infer_with_constrs ctx t] is similar to [infer ctx t] but it is
    run in constraint mode (see [constraints]). In case of success a couple of
    a type and a set of constraints is returned. *)
let infer_with_constrs : ctxt -> term -> (term * constrs) option =
  fun ctx t ->
    match in_constrs_mode (infer ctx) t with
    | (None   , _ ) ->
        if !debug_patt then
          log "patt" "unable to infer a type for [%a]" pp t;
        None
    | (Some(a), cs) ->
        if !debug_patt then
          begin
            log "patt" "inferred type [%a] for [%a]" pp a pp t;
            let fn (x,a) = log "patt" "  with\t%a\t: %a" pp_tvar x pp a in
            List.iter fn (List.rev ctx);
            let fn (a,b) = log "patt" "  where\t%a == %a" pp a pp b in
            List.iter fn cs
          end;
        Some(a, cs)

(** [subst_from_constrs cs] builds a //typing substitution// from the list  of
    constraints [cs]. The returned substitution is given by a couple of arrays
    [(xs,ts)] of the same length.  The array [xs] contains the variables to be
    substituted using the terms of [ts] at the same index. *)
let subst_from_constrs : constrs -> tvar array * term array = fun cs ->
  let rec build_sub acc cs =
    match cs with
    | []        -> acc
    | (a,b)::cs ->
        let (ha,argsa) = get_args a in
        let (hb,argsb) = get_args b in
        match (unfold ha, unfold hb) with
        | (Symb(sa), Symb(sb))
            when sa == sb && not sa.sym_definable && not sb.sym_definable ->
            let cs =
              try List.combine argsa argsb @ cs with Invalid_argument _ -> cs
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
let eq_modulo_constrs : constrs -> term -> term -> bool = fun constrs a b ->
  if !debug_patt then log "patt" "%a == %a (with constraints)" pp a pp b;
  let (xs,sub) = subst_from_constrs constrs in
  let p = Bindlib.box_pair (lift a) (lift b) in
  let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
  let (a,b) = Bindlib.msubst p sub in
  if !debug_patt then log "patt" "%a == %a (after substitution)" pp a pp b;
  eq_modulo a b

(** Representation of a rule specification, used for checking SR. *)
type rspec =
  { rspec_symbol : symbol               (** Head symbol of the rule.    *)
  ; rspec_ty_map : (string * term) list (** Type for pattern variables. *)
  ; rspec_rule   : rule                 (** The rule itself.            *) }

(** [check_rule r] check whether rule [r] is well-typed. The program
    fails gracefully in case of error. *)
let check_rule : rspec -> unit = fun spec ->
  let {rspec_symbol = s; rspec_ty_map = ty_map; rspec_rule = rule} = spec in
  (** We process the LHS to replace patterns variables by metavariables. *)
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
  let (ty_lhs, lhs_constrs) =
    match infer_with_constrs [] lhs with
    | Some(a) -> a
    | None    -> fatal "Unable to infer the type of [%a]\n" pp lhs
  in
  (* Infer the type of the RHS and the constraints. *)
  let (ty_rhs, rhs_constrs) =
    match infer_with_constrs [] rhs with
    | Some(a) -> a
    | None    -> fatal "Unable to infer the type of [%a]\n" pp rhs
  in
  (* Checking the implication of constraints. *)
  let check_constraint (a,b) =
    if not (eq_modulo_constrs lhs_constrs a b) then
      fatal "A constraint is not satisfied...\n"
  in
  List.iter check_constraint rhs_constrs;
  (* Checking if the rule is well-typed. *)
  if not (eq_modulo_constrs lhs_constrs ty_lhs ty_rhs) then
    begin
      err "Infered type for LHS: %a\n" pp ty_lhs;
      err "Infered type for RHS: %a\n" pp ty_rhs;
      fatal "[%a] is ill-typed\n" pp_rule (s, rule)
    end
