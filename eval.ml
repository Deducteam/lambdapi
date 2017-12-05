(** Evaluation and conversion. *)

open Extra
open Console
open Terms
open Print

(** [set_unif u v] sets the value of the unification variable [u] to [v]. Note
    that [u] should not have already been instanciated. *)
let set_unif : unif -> (term, term) Bindlib.mbinder -> unit = fun u v ->
  assert(unset u); u.value := Some(v);
  if !debug_unif then
    let (env,a) = Bindlib.unmbind mkfree v in
    log "unif" "?%i[%a] ← %a" u.key (Array.pp pp_tvar ",") env pp a

(** [occurs u t] checks whether the unification variable [u] occurs in [t]. *)
let rec occurs : unif -> term -> bool = fun r t ->
  match unfold t with
  | Prod(_,a,b) -> occurs r a || occurs r (Bindlib.subst b Kind)
  | Abst(_,a,t) -> occurs r a || occurs r (Bindlib.subst t Kind)
  | Appl(_,t,u) -> occurs r t || occurs r u
  | Unif(u,e)   -> u == r || Array.exists (occurs r) e
  | Type        -> false
  | Kind        -> false
  | Vari(_)     -> false
  | Symb(_)     -> false
  | ITag(_)     -> false
  | Wild        -> false

(** [unify u t] tries to unify [u] with [t], and returns a boolean to indicate
    whether it succeeded or not. Note that the function also verifies that the
    body of the unification variable (the binder) is closed. *)
let unify : unif -> term array -> term -> bool = fun u env a ->
  assert(unset u);
  not (occurs u a) &&
  let to_var t = match t with Vari v -> v | _ -> assert false in
  let b = Bindlib.bind_mvar (Array.map to_var env) (lift a) in
  Bindlib.is_closed b && (set_unif u (Bindlib.unbox b); true)

(** [to_prod r e xo] instantiates the unification variable [r] (with [e] as an
    environment) using a product type formed with fresh unification variables.
    The argument [xo] is used to name the bound variable. Note that the binder
    (the body) is constant if [xo] is equal to [None]. *)
let to_prod r e xo =
  let ra = new_unif () in
  let rb = new_unif () in
  let le = Array.map lift e in
  let a = _Unif ra le in
  let fn =
    match xo with
    | None    -> fun _ -> _Unif rb le
    | Some(_) -> fun x -> _Unif rb (Array.append le [|Bindlib.box_of_var x|])
  in
  let x = match xo with Some(x) -> x | None -> "_" in
  let p = Bindlib.unbox (_Prod a x fn) in
  if not (unify r e p) then assert false (* cannot fail *)

(** [eq t u] tests the equality of the two terms [t] and [u]. Note that during
    the comparison, unification variables may be instanciated. *)
let eq : term -> term -> bool = fun a b ->
  let rec eq a b = a == b ||
    let eq_binder = Bindlib.eq_binder mkfree eq in
    match (unfold a, unfold b) with
    | (Vari(x1)     , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Symb(Sym(s1)), Symb(Sym(s2))) -> s1 == s2
    | (Symb(Def(s1)), Symb(Def(s2))) -> s1 == s2
    | (Prod(_,a1,b1), Prod(_,a2,b2)) -> eq a1 a2 && eq_binder b1 b2
    | (Abst(_,a1,t1), Abst(_,a2,t2)) -> eq a1 a2 && eq_binder t1 t2
    | (Appl(_,t1,u1), Appl(_,t2,u2)) -> eq t1 t2 && eq u1 u2
    | (Wild         , _            ) -> assert false
    | (_            , Wild         ) -> assert false
    | (Unif(u1,e1)  , Unif(u2,e2)  ) when u1 == u2 -> assert(e1 == e2); true
    | (Unif(u,e)    , b            ) when unify u e b -> true
    | (a            , Unif(u,e)    ) -> unify u e a
    | (ITag(i1)     , ITag(i2)     ) -> i1 = i2
    | (_            , _            ) -> false
  in eq a b

(* NOTE it might be a good idea to undo unification variable instanciations in
   the case where [eq a b] returns [false]. This can be done with "timed refs"
   but for now, this does not seem to be necessary. *)

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

(* TODO cleaning from here on. *)

type stack = term ref list

let add_stack : term -> stack -> term = fun t args ->
  let rec add_stack t args =
    match args with
    | []      -> t
    | u::args -> add_stack (appl t !u) args
  in add_stack t args

(** [whnf t] returns (almost) a weak head normal form of [t]. When a reduction
    rule is matched, the arguments may need to be normalised.  Their evaluated
    form is kept to avoid useless recomputations. *)
let rec whnf : term -> term = fun t ->
  if !debug_eval then log "eval" "evaluating %a" pp t;
  let (u, stk) = whnf_stk t [] in
  let u = add_stack u stk in
  if !debug_eval then log "eval" "produced %a" pp u; u

(** [whnf_stk t stk] performs weak head normalisations of the term [t] applied
    to the argument list (or stack) [stk]. Note that the normalisation is done
    in the sense of [whnf]. *)
and whnf_stk : term -> stack -> term * stack = fun t stk ->
  match (unfold t, stk) with
  (* Push argument to the stack. *)
  | (Appl(_,f,u) , stk    )       -> whnf_stk f (ref u :: stk)
  (* Beta reduction. *)
  | (Abst(_,_,f) , u::stk )       -> whnf_stk (Bindlib.subst f !u) stk
  (* Try to rewrite. *)
  | (Symb(Def(s)), stk    ) as st ->
      begin
        match find_rule s stk with
        | None        -> st
        | Some(t,stk) -> whnf_stk t stk
      end
  (* In head normal form. *)
  | (_           , _      ) as st -> st


and find_rule : def -> stack -> (term * stack) option = fun s stk ->
  let nb_args = List.length stk in
  let match_rule r =
    (* First check that we have enough arguments. *)
    if r.arity > nb_args then None else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let new_pvar i = ITag(i) in
    let uvars =
      let ar = Bindlib.mbinder_arity r.lhs in
      Array.init ar new_pvar
    in
    let lhs = Bindlib.msubst r.lhs uvars in
    if !debug_eval then log "eval" "RULE trying rule [%a]" pp_rule (s,r);
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args lhs stk =
      match (lhs, stk) with
      | ([]    , stk   ) ->
          Some(Bindlib.msubst r.rhs (Array.map unfold uvars), stk)
      | (t::lhs, v::stk) ->
          if matching uvars t v then match_args lhs stk else None
      | (_     , _     ) -> assert false
    in
    match_args lhs stk
  in
  let rec find rs =
    match rs with
    | []    -> None
    | r::rs ->
        match match_rule r with
        | None -> find rs
        | res  -> res
  in
  find s.def_rules

and matching ar pat t =
  if !debug_eval then log "matc" "[%a] =~= [%a]" pp pat pp !t;
  let res =
    match pat with
    | ITag(i) ->
        if ar.(i) = ITag(i) then (ar.(i) <- !t; true)
        else eq_modulo ar.(i) !t
    | Wild    -> true
    | _ ->
    match (pat, (t := whnf !t; !t)) with
    | (Prod(_,a1,b1), Prod(_,a2,b2)) ->
        let (_,b1,b2) = Bindlib.unbind2 mkfree b1 b2 in
        matching ar a1 (ref a2) && matching ar b1 (ref b2)
    | (Abst(_,_,t1) , Abst(_,_,t2) ) ->
        let (_,t1,t2) = Bindlib.unbind2 mkfree t1 t2 in
        matching ar t1 (ref t2)
    | (Appl(_,t1,u1), Appl(_,t2,u2)) ->
        matching ar t1 (ref t2) && matching ar u1 (ref u2)
    | (Unif(_,_)    , _            ) -> assert false
    | (_            , Unif(_,_)    ) -> assert false
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Vari(x1)     , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Symb(s1)     , Symb(s2)     ) -> s1 == s2
    | (_            , _            ) -> false
  in
  if !debug_eval then
    log "matc" (r_or_g res "[%a] =~= [%a]") pp pat pp !t;
  res

and eq_modulo : ?constr_on:bool -> term -> term -> bool =
  fun ?(constr_on=false) a b ->
  if !debug_equa then log "equa" "%a == %a" pp a pp b;
  let rec eq_modulo l =
    match l with
    | []                   -> true
    | (a,b)::l when eq a b -> eq_modulo l
    | (a,b)::l             ->
        let (a,sa) = whnf_stk a [] in
        let (b,sb) = whnf_stk b [] in
        let rec sync acc la lb =
          match (la, lb) with
          | ([]   , []   ) -> (a, b, List.rev acc)
          | (a::la, b::lb) -> sync ((!a,!b)::acc) la lb
          | (la   , []   ) -> (add_stack a (List.rev la), b, acc)
          | ([]   , lb   ) -> (a, add_stack b (List.rev lb), acc)
        in
        let (a,b,l) = sync l (List.rev sa) (List.rev sb) in
        let a = unfold a in
        let b = unfold b in
        match (a, b) with
        | (_            , _            ) when eq a b -> eq_modulo l
        | (Appl(_,_,_)  , Appl(_,_,_)  ) -> eq_modulo ((a,b)::l)
        | (Abst(_,aa,ba), Abst(_,ab,bb)) ->
            let x = mkfree (Bindlib.new_var mkfree "_eq_modulo_") in
            eq_modulo ((aa,ab)::(Bindlib.subst ba x, Bindlib.subst bb x)::l)
        | (Prod(_,aa,ba), Prod(_,ab,bb)) ->
            let x = mkfree (Bindlib.new_var mkfree "_eq_modulo_") in
            eq_modulo ((aa,ab)::(Bindlib.subst ba x, Bindlib.subst bb x)::l)
        | (a            , b            ) ->
            constr_on && add_constraint a b && eq_modulo l
  in
  let res = eq_modulo [(a,b)] in
  if !debug_equa then log "equa" (r_or_g res "%a == %a") pp a pp b; res
