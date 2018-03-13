(** Type-checking and inference. *)

open Console
open Terms
open Print
open Eval
open Unif
open Typing

(** [infer_with_constrs sign ctx t] is similar to [infer sign ctx t] but it is
    run in constraint mode (see [constraints]). In case of success a couple of
    a type and a set of constraints is returned. *)
let infer_with_constrs : Sign.t -> Ctxt.t -> term -> (term * constrs) option =
  fun sign ctx t ->
    match in_constrs_mode (infer sign ctx) t with
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
        | (Symb(Sym(sa)), Symb(Sym(sb))) when sa == sb ->
            let cs =
              try List.combine argsa argsb @ cs with Invalid_argument _ -> cs
            in
            build_sub acc cs
        | (Symb(Def(sa)), Symb(Def(sb))) when sa == sb ->
            wrn "%s may not be injective...\n%!" sa.def_name;
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

(** [check_rule sign r] check whether rule [r] is well-typed, in the signature
    [sign]. The program fails gracefully in case of error. *)
let check_rule sign (ctx, s, t, u, rule) =
  (* Infer the type of the LHS and the constraints. *)
  let (tt, tt_constrs) =
    match infer_with_constrs sign ctx t with
    | Some(a) -> a
    | None    -> fatal "Unable to infer the type of [%a]\n" pp t
  in
  (* Infer the type of the RHS and the constraints. *)
  let (tu, tu_constrs) =
    match infer_with_constrs sign ctx u with
    | Some(a) -> a
    | None    -> fatal "Unable to infer the type of [%a]\n" pp u
  in
  (* Checking the implication of constraints. *)
  let check_constraint (a,b) =
    if not (eq_modulo_constrs tt_constrs a b) then
      fatal "A constraint is not satisfied...\n"
  in
  List.iter check_constraint tu_constrs;
  (* Checking if the rule is well-typed. *)
  if not (eq_modulo_constrs tt_constrs tt tu) then
    begin
      err "Infered type for LHS: %a\n" pp tt;
      err "Infered type for RHS: %a\n" pp tu;
      fatal "[%a → %a] is ill-typed\n" pp t pp u
    end;
  (* Adding the rule. *)
  (s,t,u,rule)
