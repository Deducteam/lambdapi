(** Type-checking and inference. *)

open Bindlib
open Console
open Terms
open Print
open Eval

(* [infer sign ctx t] tries to infer a type for the term [t], in context [ctx]
   and with the signature [sign]. [Some a] is returned if type [a] is inferred
   and [None] is returned otherwise. *)
let rec infer : Sign.t -> Ctxt.t -> term -> term option = fun sign ctx t ->
  let env = List.map (fun (x,_) -> box_of_var x) ctx in
  let a = unbox (_Unif (new_unif ()) (Array.of_list env)) in
  if has_type sign ctx t a then Some(eval a) else None

(* [has_type sign ctx t a] checks whether the term [t] has type [a] in context
   [ctx] and with the signature [sign]. *)
and has_type : Sign.t -> Ctxt.t -> term -> term -> bool = fun sign ctx t c ->
  if !debug_type then log "TYPE" "%a ⊢ %a : %a%!" pp_ctxt ctx pp t pp c;
  let res =
  match unfold t with
  (* Sort *)
  | Type        -> eq_modulo c Kind
  (* Variable *)
  | Vari(x)     -> (try eq_modulo (Ctxt.find x ctx) c with Not_found ->
                      wrn "BUG0 (%a not in context) \n" pp_tvar x; false)
  (* Symbol *)
  | Symb(s)     -> eq_modulo (symbol_type s) c
  (* Product *)
  | Prod(_,a,b) ->
      let (x,bx) = unbind mkfree b in
      let ctx_x = if binder_occur b then Ctxt.add x a ctx else ctx in
      has_type sign ctx_x bx c &&
      has_type sign ctx a Type &&
      begin
        match eval c with
        | Type -> true
        | Kind -> true
        | a     -> wrn "BUG1 ([%a] not a sort)\n" pp a; false
      end
  (* Abstraction *)
  | Abst(_,a,t) ->
      begin
        let (x,tx) = unbind mkfree t in
        let c =
          match eval c with
          | Unif(r,e) as c ->
              let rb = new_unif () in
              let eb = Array.map lift e in
              let f x = _Unif rb (Array.append eb [|box_of_var x|]) in
              let p = _Prod (lift a) (Bindlib.binder_name t) f in
              unify r e (Bindlib.unbox p); unfold c
          | c              -> c
        in
        match c with
        | Unif(_,_)   -> assert false
        | Prod(_,c,b) ->
            let bx = subst b (mkfree x) in
            let ctx_x = Ctxt.add x a ctx in
            eq_modulo a c &&
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
            false
      end
  (* Application *)
  | Appl(_,t,u) ->
      begin
        match infer sign ctx t with
        | Some(Prod(_,a,ba)) ->
            eq_modulo (Bindlib.subst ba u) c
            && has_type sign ctx u a
        | Some(Unif(r,env))  ->
            let a = _Unif (new_unif ()) (Array.map lift env) in
            let b = Bindlib.unbox (_Prod a "_" (fun _ -> lift c)) in
            assert(unify r env b);
            has_type sign ctx u (Bindlib.unbox a)
        | Some(a)            ->
            err "Product type expected for [%a], found [%a]..." pp t pp a;
            false
        | None               ->
            wrn "Cannot infer the type of [%a]\n%!" pp t;
            false
      end
  (* No rule apply. *)
  | Kind        -> assert false
  | ITag(_)     -> assert false
  | Unif(_,_)   -> assert false
  in
  if !debug_type then
    log "TYPE" (r_or_g res "%a ⊢ %a : %a") pp_ctxt ctx pp t pp c;
  res

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

let has_type : Sign.t -> Ctxt.t -> term -> term -> bool = fun sign ctx t c ->
  if !debug then log "type" "%a ⊢ %a : %a" pp_ctxt ctx pp t pp c;
  let res = has_type sign ctx t c in
  if !debug then log "type" (r_or_g res "%a ⊢ %a : %a") pp_ctxt ctx pp t pp c;
  res

(* [infer_with_constrs sign ctx t] is similar to [infer sign ctx t], but it is
   run in constraint mode (see [constraints]).  In case of success a couple of
   a type and a set of constraints is returned. *)
let infer_with_constrs : Sign.t -> Ctxt.t -> term -> (term * constrs) option =
  fun sign ctx t ->
    constraints := Some [];
    match infer sign ctx t with
    | None   -> constraints := None; None
    | Some a ->
        let cnstrs = match !constraints with Some cs -> cs | None -> [] in
        constraints := None;
        if !debug_patt then
        begin
          log "patt" "inferred type [%a] for [%a]" pp a pp t;
          let fn (x,a) =
            log "patt" "  with\t%s\t: %a" (Bindlib.name_of x) pp a
          in
          List.iter fn (List.rev ctx);
          let fn (a,b) = log "patt" "  where\t%a == %a" pp a pp b in
          List.iter fn cnstrs
        end;
        Some(a, cnstrs)

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

(* [sort_type sign x a] finds out the sort of the type [a],  which corresponds
   to variable [x]. The result may be either [Type] or [Kind]. If [a] is not a
   well-sorted type, then the program fails gracefully. *)
let sort_type : Sign.t -> string -> term -> term = fun sign x a ->
  match infer sign Ctxt.empty a with
  | Some(Kind) -> Kind
  | Some(Type) -> Type
  | Some(a)    -> fatal "%s is neither of type Type nor Kind.\n" x
  | None       -> fatal "cannot infer the sort of %s.\n" x
