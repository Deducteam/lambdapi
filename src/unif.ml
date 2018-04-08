(** Evaluation and conversion. *)

open Extra
open Console
open Terms
open Print
open Eval

(** [set_meta u v] sets the value of the metavariable [m] to [v]. Note
    that [m] should not have already been instanciated. *)
let set_meta : meta -> (term, term) Bindlib.mbinder -> unit = fun m v ->
  m.meta_value := Some(v);
  if !debug_meta then
    let (env,a) = Bindlib.unmbind mkfree v in
    log "meta" "?%i[%a] ← %a" m.meta_key (Array.pp pp_tvar ",") env pp a

(** [occurs u t] checks whether the metavariable [u] occurs in [t]. *)
let rec occurs : meta -> term -> bool = fun r t ->
  match unfold t with
  | Prod(a,b) -> occurs r a || occurs r (Bindlib.subst b Kind)
  | Abst(a,t) -> occurs r a || occurs r (Bindlib.subst t Kind)
  | Appl(t,u) -> occurs r t || occurs r u
  | Meta(u,e) -> u == r || Array.exists (occurs r) e
  | Type      -> false
  | Kind      -> false
  | Vari(_)   -> false
  | Symb(_)   -> false
  | ITag(_)   -> false
  | Wild      -> false

(** [instantiate u t] tries to instantiate [u] with [t], and returns a boolean
    telling whether it succeeded or not.  Note that the function also verifies
    that the body of the metavariable (the binder) is closed. *)
let instantiate : meta -> term array -> term -> bool = fun u env a ->
  assert(unset u);
  not (occurs u a) &&
  let to_var t = match t with Vari v -> v | _ -> assert false in
  let b = Bindlib.bind_mvar (Array.map to_var env) (lift a) in
  Bindlib.is_closed b && (set_meta u (Bindlib.unbox b); true)
    
(** [unify t u] tests the equality of the two terms [t] and [u] while possibly
    instantiating metavariables. *)
let unify : term -> term -> bool = fun a b ->
  let rec unify a b = a == b ||
    let unify_binder = Bindlib.eq_binder mkfree unify in
    match (unfold a, unfold b) with
    | (Vari(x1)     , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Symb(Sym(s1)), Symb(Sym(s2))) -> s1 == s2
    | (Symb(Def(s1)), Symb(Def(s2))) -> s1 == s2
    | (Prod(a1,b1)  , Prod(a2,b2)  ) -> unify a1 a2 && unify_binder b1 b2
    | (Abst(a1,t1)  , Abst(a2,t2)  ) -> unify a1 a2 && unify_binder t1 t2
    | (Appl(t1,u1)  , Appl(t2,u2)  ) -> unify t1 t2 && unify u1 u2
    | (Wild         , _            ) -> assert false
    | (_            , Wild         ) -> assert false
    | (ITag(_)      , _            ) -> assert false
    | (_            , ITag(_)      ) -> assert false
    | (Meta(u1,e1)  , Meta(u2,e2)  ) when u1 == u2 -> assert(e1 == e2); true
    | (Meta(u,e)    , b            ) when instantiate u e b -> true
    | (a            , Meta(u,e)    ) -> instantiate u e a
    | (_            , _            ) -> false
  in unify a b

(* NOTE it might be a good idea to undo metavariable instantiations in
   the case where [unify a b] returns [false].  This can be achieved using the
   "timed refs" approach, but this does not seem to be necessary for now. *)

(** Representation of equality constraints. *)
type constrs = (term * term) list

(** If [constraints] is set to [None] then typechecking is in regular mode. If
    it is set to [Some l] then it is in constraint mode, which means that when
    equality fails a constraint is added to [constrs] instead of the  equality
    function giving up. *)
let constraints = ref None

(* NOTE: constraint mode is only used when type-cheching the left-hand side of
   reduction rules (see function [infer_with_constrs] for mode switching). *)

(** [in_constrs_mode f a] enters constraint mode, runs [f a], exits constraint
    mode and returns the result of the computation with the constraints. *)
let in_constrs_mode : ('a -> 'b) -> 'a -> 'b * constrs = fun f a ->
  constraints := Some([]);
  let res = f a in
  let cs = match !constraints with Some(cs) -> cs | None -> assert false in
  constraints := None; (res, cs)

(** [add_constraint a b] adds an equality constraint between [a] and [b] while
    returning [true], when the program is in constraint mode. When the program
    is in regular mode, the value [false] is immediately returned. *)
let add_constraint : term -> term -> bool = fun a b ->
  match !constraints with
  | None    -> false
  | Some(l) ->
      if !debug_patt then log "cnst" "new constraint [%a == %a]." pp a pp b;
      constraints := Some((a, b)::l); true

(** [unify_modulo a b] tests equality modulo rewriting between  the
    terms [a] and [b]. *)
(*
let unify_modulo : term -> term -> bool = fun a b ->
  if !debug_equa then log "unif" "%a == %a" pp a pp b;
  let rec unify_modulo l =
    if l <> [] && !debug_equa then
      begin
        let f oc (a,b) = Printf.fprintf oc "        - %a == %a" pp a pp b in
        log "unif" "List of equations to prove:\n%a" (List.pp f "\n") l;
      end;
    match l with
    | []                      -> true
    | (a,b)::l when unify a b -> unify_modulo l
    | (a,b)::l                ->
        let (a,sa) = whnf_stk a [] in
        let (b,sb) = whnf_stk b [] in
        let rec sync acc la lb =
          match (la, lb) with
          | ([]   , []   ) -> (a, b, acc)
          | (a::la, b::lb) -> sync ((!a,!b)::acc) la lb
          | (la   , []   ) -> (to_term a (List.rev la), b, acc)
          | ([]   , lb   ) -> (a, to_term b (List.rev lb), acc)
        in
        let (a,b,l') = sync [] (List.rev sa) (List.rev sb) in
        match (a, b) with
        | (Symb(Sym(sa)), Symb(Sym(sb))) ->
            sa == sb && unify_modulo (l' @ l)
        | (Abst(aa,ba)  , Abst(ab,bb)  ) ->
            assert (l' = []);
            let (_,ba,bb) = Bindlib.unbind2 mkfree ba bb in
            unify_modulo ((aa,ab)::(ba,bb)::l)
        | (Prod(aa,ba)  , Prod(ab,bb)  ) ->
            assert (l' = []);
            let (_,ba,bb) = Bindlib.unbind2 mkfree ba bb in
            unify_modulo ((aa,ab)::(ba,bb)::l)
        | (a            , b            ) ->
            let fn (a,b) = unify a b || add_constraint a b in
            List.for_all fn ((a,b)::l') && unify_modulo l
  in
  let res = unify_modulo [(a,b)] in
  if !debug_equa then log "unif" (r_or_g res "%a == %a") pp a pp b; res
  *)

let unify_modulo : term -> term -> bool = fun a b ->
  if !debug_equa then log "unif" "%a == %a" pp a pp b;
  let rec unify_modulo a b = eq a b ||
    let a = whnf a in
    let b = whnf b in
    let rec get_args l a b =
      match (unfold a, unfold b) with
      | (Appl(t1,u1), Appl(t2,u2)) -> get_args ((u1,u2)::l) t1 t2
      | (Meta(u1,e1), Meta(u2,e2)) when u1 == u2 -> (a,b,l)
      | (Meta(m,e)  , b          ) when instantiate m e b -> get_args l a b
      | (a          , Meta(m,e)  ) when instantiate m e a -> get_args l a b
      | (_          , Meta(_,_)  ) -> assert false
      | (_          , _          ) -> (a,b,l)
    in
    let unif =
      match !constraints with
      | None -> unify_modulo
      | _    -> unify
    in
    let (a,b,l) = get_args [] a b in
    let l = List.rev l in
    match (unfold a, unfold b) with
    | (Wild         , _            ) -> assert false
    | (_            , Wild         ) -> assert false
    | (ITag(_)      , _            ) -> assert false
    | (_            , ITag(_)      ) -> assert false
    | (Type         , Type         ) -> assert (l = []); true
    | (Kind         , Kind         ) -> assert (l = []); true
    | (Prod(a1,b1)  , Prod(a2,b2)  ) ->
        assert (l = []);
        unify_modulo a1 a2 &&
        unify_modulo_binder b1 b2
    | (Abst(a1,t1)  , Abst(a2,t2)  ) ->
        assert (l = []);
        unify_modulo a1 a2 &&
        unify_modulo_binder t1 t2
    | (Vari(x1)     , Vari(x2)     ) when Bindlib.eq_vars x1 x2 ->
        List.for_all (fun (a,b) -> unif a b || add_constraint a b) l
    | (Symb(Sym(s1)), Symb(Sym(s2))) ->
        s1 == s2 &&
        List.for_all (fun (a,b) -> unify_modulo a b) l
    | (Symb(Def(s1)), Symb(Def(s2))) when s1 == s2 && l = [] -> true
    | (Meta(u1,e1)  , Meta(u2,e2)  ) ->
        u1 == u2 &&
        Array.for_all2 (fun a b -> unif a b || add_constraint a b) e1 e2 &&
        List.for_all (fun (a,b) -> unif a b || add_constraint a b) l
    | (a            , b            ) ->
        match !constraints with
        | None -> unify a b && List.for_all (fun (a,b) -> unif a b) l
        | _    ->
            let a = add_args a (List.map fst l) in
            let b = add_args b (List.map snd l) in
            add_constraint a b
  and unify_modulo_binder b1 b2 =
    let (_,a1,a2) = Bindlib.unbind2 mkfree b1 b2 in
    unify_modulo a1 a2
  in
  let res = unify_modulo a b in
  if !debug_equa then log "unif" (r_or_g res "%a == %a") pp a pp b; res
