(** Type-checking and inference. *)

open Console
open Terms
open Print
open Eval

(** [infer sign ctx t] tries to infer a type for the term [t] in context [ctx]
    and with the signature [sign]. If the function is not able to infer a type
    then [None] is returned. Otherwise, [Some a] is returned, where [a] is the
    (fully evaluated) infered type. *)
let rec infer : Sign.t -> Ctxt.t -> term -> term option = fun sign ctx t ->
  let env = List.map (fun (x,_) -> Bindlib.box_of_var x) ctx in
  let a = Bindlib.unbox (_Unif (new_unif ()) (Array.of_list env)) in
  if has_type sign ctx t a then Some(whnf a) else None

(** [has_type sign ctx t a] tests whether the term [t] has type [a] in context
    [ctx] and with the signature [sign]. Note that inference can be  performed
    using an [a] that is a unification variable. *)
and has_type : Sign.t -> Ctxt.t -> term -> term -> bool = fun sign ctx t c ->
  if !debug_type then log "TYPE" "%a ⊢ %a : %a%!" pp_ctxt ctx pp t pp c;
  let res =
    match unfold t with
    (* Sort *)
    | Type        ->
        eq c Kind
    (* Variable *)
    | Vari(x)     ->
        let cx = try Ctxt.find x ctx with Not_found -> assert false in
        eq_modulo ~constr_on:true cx c
    (* Symbol *)
    | Symb(s)     ->
        eq_modulo ~constr_on:true (symbol_type s) c
    (* Product *)
    | Prod(_,a,b) ->
        begin
          let (x,bx) = Bindlib.unbind mkfree b in
          let uses_x = Bindlib.binder_occur b in
          has_type sign (if uses_x then Ctxt.add x a ctx else ctx) bx c &&
          has_type sign ctx a Type &&
          match whnf c with
          | Type -> true | Kind -> true
          | c    -> err "[%a] is not a sort...\n" pp c; false
        end
    (* Abstraction *)
    | Abst(_,a,t) ->
        begin
          let (x,tx) = Bindlib.unbind mkfree t in
          let c = whnf c in
          begin
            match c with
            | Unif(r,e) -> to_prod r e (Some(Bindlib.binder_name t))
            | _         -> ()
          end;
          match unfold c with
          | Prod(_,c,b) ->
              let bx = Bindlib.subst b (mkfree x) in
              let ctx_x = Ctxt.add x a ctx in
              eq_modulo ~constr_on:true a c &&
              has_type sign ctx_x tx bx &&
              has_type sign ctx a Type &&
              begin
                match infer sign ctx_x bx with
                | Some(Type) -> true
                | Some(Kind) -> true
                | Some(a)    -> wrn "BUG3 ([%a] not a sort)\n" pp a; false
                | None       -> wrn "BUG3 (cannot infer sort)\n"; false
              end
          | c           ->
              err "Product type expected, found [%a]...\n" pp c;
              assert(unfold c == c); false
        end
    (* Application *)
    | Appl(_,t,u) ->
        begin
          match infer sign ctx t with
          | None    -> wrn "Cannot infer the type of [%a]\n%!" pp t; false
          | Some(a) ->
              begin
                begin
                  match a with
                  | Unif(r,e) -> to_prod r e None
                  | _         -> ()
                end;
                match unfold a with
                | Prod(_,a,b) ->
                    eq_modulo ~constr_on:true (Bindlib.subst b u) c
                    && has_type sign ctx u a
                | a           ->
                    err "Product expected for [%a], found [%a]...\n%!"
                      pp t pp a;
                    assert(unfold c == c); false
              end
        end
    (* No rule apply. *)
    | Kind        -> assert false
    | ITag(_)     -> assert false
    | Unif(_,_)   -> assert false
    | Wild        -> assert false
  in
  if !debug_type then
    log "TYPE" (r_or_g res "%a ⊢ %a : %a") pp_ctxt ctx pp t pp c;
  res

(** [infer sign ctx t] is a wrapper function for the [infer] function  defined
    earlier. It is mainly used to obtain fine-grained logs. *)
let infer : Sign.t -> Ctxt.t -> term -> term option = fun sign ctx t ->
  if !debug then log "infr" "%a ⊢ %a : ?" pp_ctxt ctx pp t;
  let res = infer sign ctx t in
  if !debug then
    begin
      match res with
      | Some(a) -> log "infr" (gre "%a ⊢ %a : %a") pp_ctxt ctx pp t pp a
      | None    -> err "Cannot infer the type of [%a]\n" pp t
    end;
  res

(** [has_type sign ctx t a] is a wrapper function for the [has_type]  function
    defined earlier. It is mainly used to obtain fine-grained logs. *)
let has_type : Sign.t -> Ctxt.t -> term -> term -> bool = fun sign ctx t c ->
  if !debug then log "type" "%a ⊢ %a : %a" pp_ctxt ctx pp t pp c;
  let res = has_type sign ctx t c in
  if !debug then log "type" (r_or_g res "%a ⊢ %a : %a") pp_ctxt ctx pp t pp c;
  res

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

(** [sort_type sign a] infers the sort of the type [a].  The result may either
    be [Type] or [Kind]. If [a] is not a well-sorted type then the program fails
    gracefully. *)
let sort_type : Sign.t -> term -> term = fun sign a ->
  match infer sign Ctxt.empty a with
  | Some(Kind) -> Kind
  | Some(Type) -> Type
  | Some(s)    -> fatal "[%a] has type [%a] (not a sort)...\n" pp a pp s
  | None       -> fatal "cannot infer the sort of [%a]...\n" pp a

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
