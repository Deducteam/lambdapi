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
  | Prod(_,a,b) -> occurs r a || occurs r (Bindlib.subst b Kind)
  | Abst(_,a,t) -> occurs r a || occurs r (Bindlib.subst t Kind)
  | Appl(_,t,u) -> occurs r t || occurs r u
  | Meta(u,e)   -> u == r || Array.exists (occurs r) e
  | Type        -> false
  | Kind        -> false
  | Vari(_)     -> false
  | Symb(_)     -> false
  | ITag(_)     -> false
  | Wild        -> false

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
    | (Prod(_,a1,b1), Prod(_,a2,b2)) -> unify a1 a2 && unify_binder b1 b2
    | (Abst(_,a1,t1), Abst(_,a2,t2)) -> unify a1 a2 && unify_binder t1 t2
    | (Appl(_,t1,u1), Appl(_,t2,u2)) -> unify t1 t2 && unify u1 u2
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
let unify_modulo : term -> term -> bool = fun a b ->
  if !debug_equa then log "unif" "%a == %a" pp a pp b;
  let rec unify_modulo l =
    match l with
    | []                   -> true
    | (a,b)::l when unify a b -> unify_modulo l
    | (a,b)::l             ->
        let (a,sa) = whnf_stk a [] in
        let (b,sb) = whnf_stk b [] in
        let rec sync acc la lb =
          match (la, lb) with
          | ([]   , []   ) -> (a, b, acc)
          | (a::la, b::lb) -> sync ((!a,!b)::acc) la lb
          | (la   , []   ) -> (to_term a (List.rev la), b, acc)
          | ([]   , lb   ) -> (a, to_term b (List.rev lb), acc)
        in
        let (a,b,l) = sync l (List.rev sa) (List.rev sb) in
        match (a, b) with
        | (a            , b            ) when unify a b -> unify_modulo l
        | (Abst(_,aa,ba), Abst(_,ab,bb)) ->
            let (_,ba,bb) = Bindlib.unbind2 mkfree ba bb in
            unify_modulo ((aa,ab)::(ba,bb)::l)
        | (Prod(_,aa,ba), Prod(_,ab,bb)) ->
            let (_,ba,bb) = Bindlib.unbind2 mkfree ba bb in
            unify_modulo ((aa,ab)::(ba,bb)::l)
        | (a            , b            ) ->
            add_constraint a b && unify_modulo l
  in
  let res = unify_modulo [(a,b)] in
  if !debug_equa then log "unif" (r_or_g res "%a == %a") pp a pp b; res
