open Extra
open Console
open Files
open Terms
open Eq
open Eval
open Conv

(* [infer sign ctx t] tries to infer a type for the term [t], in context [ctx]
   and with the signature [sign].  The exception [Not_found] is raised when no
   suitable type is found. *)
let rec infer : Sign.t -> Ctxt.t -> term -> term = fun sign ctx t ->
  let rec infer ctx t =
    if !debug_infr then log "INFR" "%a ⊢ %a : ?" Ctxt.pp ctx pp t;
    let a =
      match unfold t with
      | Vari(x)     -> Ctxt.find x ctx
      | Type        -> Kind
      | Symb(s)     -> symbol_type s
      | Prod(_,a,b) ->
          let (x,bx) = Bindlib.unbind mkfree b in
          begin
            match infer (Ctxt.add x a ctx) bx with
            | Kind -> Kind
            | Type -> Type
            | a    -> err "Type or Kind expected for [%a], found [%a]...\n"
                        pp bx pp a;
                      raise Not_found
          end
      | Abst(_,a,t) ->
          let (x,tx) = Bindlib.unbind mkfree t in
          let b = infer (Ctxt.add x a ctx) tx in
          prod a (Bindlib.unbox (Bindlib.bind_var x (lift b)))
      | Appl(_,t,u) ->
          begin
            match unfold (infer ctx t) with
            | Prod(_,a,b) when has_type sign ctx u a -> Bindlib.subst b u
            | Prod(_,a,_)                            ->
                err "Cannot show [%a : %a]...\n" pp u pp a;
                raise Not_found
            | a                                      ->
                err "Product expected for [%a], found [%a]...\n" pp t pp a;
                raise Not_found
          end
      | Kind        -> assert false
      | Unif(_)     -> assert false
      | PVar(_)     -> assert false
    in
    if !debug_infr then log "INFR" "%a ⊢ %a : %a" Ctxt.pp ctx pp t pp a;
    eval a
  in
  if !debug then log "infr" "%a ⊢ %a : ?" Ctxt.pp ctx pp t;
  let res = infer ctx t in
  if !debug then log "infr" "%a ⊢ %a : %a" Ctxt.pp ctx pp t pp res; res

(* [has_type sign ctx t a] checks whether the term [t] has type [a] in context
   [ctx] and with the signature [sign]. *)
and has_type : Sign.t -> Ctxt.t -> term -> term -> bool = fun sign ctx t a ->
  let rec has_type ctx t a =
    let t = unfold t in
    let a = eval a in
    if !debug_type then log "TYPE" "%a ⊢ %a : %a" Ctxt.pp ctx pp t pp a;
    let res =
      match (t, a) with
      (* Sort *)
      | (Type       , Kind       ) -> true
      (* Variable *)
      | (Vari(x)    , a          ) -> eq_modulo (Ctxt.find x ctx) a
      (* Symbol *)
      | (Symb(s)    , a          ) -> eq_modulo (symbol_type s) a
      (* Product *)
      | (Prod(_,a,b), s          ) ->
          let (x,bx) = Bindlib.unbind mkfree b in
          let ctx_x =
            if Bindlib.binder_occur b then Ctxt.add x a ctx else ctx
          in
          has_type ctx a Type && has_type ctx_x bx s
          && (eq s Type || eq s Kind)
      (* Abstraction *)
      | (Abst(_,a,t), Prod(_,c,b)) ->
          let (x,tx) = Bindlib.unbind mkfree t in
          let bx = Bindlib.subst b (mkfree x) in
          let ctx_x = Ctxt.add x a ctx in
          eq_modulo a c && has_type ctx a Type
          && (has_type ctx_x bx Type || has_type ctx_x bx Kind)
          && has_type ctx_x tx bx
      (* Application *)
      | (Appl(_,t,u), b          ) ->
          begin
            let tt = infer sign ctx t in
            match tt with
            | Prod(_,a,ba) ->
                eq_modulo (Bindlib.subst ba u) b
                && has_type ctx t tt && has_type ctx u a
            | Unif(r,env)  ->
                let a = Unif(ref None, env) in
                let b = Bindlib.bind mkfree "_" (fun _ -> lift b) in
                let b = prod a (Bindlib.unbox b) in
                assert(unify r env b);
                has_type ctx t tt && has_type ctx u a
            | _            -> false
          end
      (* No rule apply. *)
      | (_          , _          ) -> false
    in
    if !debug_type then
      log "TYPE" (r_or_g res "%a ⊢ %a : %a") Ctxt.pp ctx pp t pp a;
    res
  in
  if !debug then log "type" "%a ⊢ %a : %a" Ctxt.pp ctx pp t pp a;
  let res = has_type ctx t a in
  if !debug then log "type" (r_or_g res "%a ⊢ %a : %a") Ctxt.pp ctx pp t pp a;
  res

(* [infer_with_constrs sign ctx t] is similar to [infer sign ctx t], but it is
   run in constraint mode (see [constraints]).  In case of success a couple of
   a type and a set of constraints is returned. In case of failure [Not_found]
   is raised. *)
let infer_with_constrs : Sign.t -> Ctxt.t -> term -> term * constrs =
  fun sign ctx t ->
    constraints := Some [];
    let a = infer sign ctx t in
    let cnstrs = match !constraints with Some cs -> cs | None -> [] in
    constraints := None;
    if !debug_patt then
      begin
        log "patt" "inferred type [%a] for [%a]" pp a pp t;
        let fn (x,a) =
          log "patt" "  with\t%s\t: %a" (Bindlib.name_of x) pp a
        in
        List.iter fn ctx;
        let fn (a,b) = log "patt" "  where\t%a == %a" pp a pp b in
        List.iter fn cnstrs
      end;
    (a, cnstrs)

(* [subst_from_constrs cs] builds a //typing substitution// from the  list  of
   constraints [cs].  The returned substitution is given by a couple of arrays
   [(xs,ts)] of the same length. The array [ts] contains the terms that should
   be substituted to the corresponding variables of [xs]. *)
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

(* [eq_modulo_constrs cs t u] checks if [t] and [u] are equal modulo rewriting
   given a list of constraints [cs] (assumed to be all satisfied). *)
let eq_modulo_constrs : constrs -> term -> term -> bool =
  fun constrs a b -> eq_modulo a b ||
    let (xs,sub) = subst_from_constrs constrs in
    let p = Bindlib.box_pair (lift a) (lift b) in
    let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
    let (a,b) = Bindlib.msubst p sub in
    eq_modulo a b
