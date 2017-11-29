(** Evaluation and conversion. *)

open Extra
open Console
open Terms
open Print

(** [set_unif u v] sets the value of the unification variable [u] to [v]. Note
    that [u] should not have already been instanciated. *)
let set_unif : unif -> (term, term) Bindlib.mbinder -> unit = fun u v ->
  assert(u.value = None); u.value <- Some(v);
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

(** [unify u t] tries to unify [u] with [t], and returns a boolean to indicate
    whether it succeeded or not. Note that the function also verifies that the
    body of the unification variable (the binder) is closed. *)
let unify : unif -> term array -> term -> bool = fun u env a ->
  assert (u.value = None);
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

(* TODO cleaning from here on. *)

type eval_fun = term -> term list -> term * term list

(* [eq t u] tests the equality of the terms [t] and [u]. Pattern variables may
   be instantiated in the process. *)
let eq : term -> term -> bool = fun a b ->
  let rec eq a b = a == b ||
    let eq_binder = Bindlib.eq_binder mkfree eq in
    match (unfold a, unfold b) with
    | (Vari(x)      , Vari(y)      ) -> Bindlib.eq_vars x y
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Symb(Sym(sa)), Symb(Sym(sb))) -> sa == sb
    | (Symb(Def(sa)), Symb(Def(sb))) -> sa == sb
    | (Prod(_,a,f)  , Prod(_,b,g)  ) -> eq a b && eq_binder f g
    | (Abst(_,a,f)  , Abst(_,b,g)  ) -> eq a b && eq_binder f g
    | (Appl(_,t,u)  , Appl(_,f,g)  ) -> eq t f && eq u g
    | (Unif(u1,e1)  , Unif(u2,e2)  ) when u1 == u2 -> Array.for_all2 eq e1 e2
    | (Unif(u,e)    , b            ) when unify u e b -> true
    | (a            , Unif(u,e)    ) -> unify u e a
    | (ITag(i1)     , ITag(i2)     ) -> i1 = i2
    | (_            , _            ) -> false
  in
  eq a b

(* Representation of equality constraints. *)
type constrs = (term * term) list

(* If [constraints] is set to [None], then typechecking is in regular mode. If
   it is set to [Some(l)] then it is in constraint mode, which means that when
   equality fails, an equality constraint is added to [constrs] instead of the
   equality function giving up. *)
let constraints = ref None

(* NOTE: constraint mode is only used when type-cheching the left-hand side of
   reduction rules (see function [infer_with_constrs] for mode switching). *)

(* [add_constraint a b] adds an equality constraint between [a] and [b] if the
   program is in regular mode. In this case it returns [true].  If the program
   is in regular mode, then [false] is returned immediately. *)
let add_constraint : term -> term -> bool = fun a b ->
  match !constraints with
  | None    -> false
  | Some(l) ->
      if !debug then log "cnst" "adding constraint [%a == %a]." pp a pp b;
      constraints := Some((a, b)::l); true

let rec whnf_stk : term -> term list -> term * term list = fun t stk ->
  let t = unfold t in
  match (t, stk) with
  (* Push argument to the stack. *)
  | (Appl(_,f,u) , stk    ) -> whnf_stk f (u :: stk)
  (* Beta reduction. *)
  | (Abst(_,_,f) , u::stk ) -> whnf_stk (Bindlib.subst f u) stk
  (* Try to rewrite. *)
  | (Symb(Def(s)), stk    ) ->
      begin
        match match_rules s stk with
        | []          ->
            (* No rule applies. *)
            (t, stk)
        | (t,stk)::rs ->
            (* At least one rule applies. *)
            if !debug_eval && rs <> [] then
              wrn "%i rules apply...\n%!" (List.length rs);
            (* Just use the first one. *)
            whnf_stk t stk
      end
  (* In head normal form. *)
  | (_           , _      ) -> (t, stk)

(* [match_rules s stk] tries to apply the reduction rules of symbol [s]  using
   the stack [stk]. The possible abstract machine states (see [eval_stk]) with
   which to continue are returned. *)
and match_rules : def -> term list -> (term * term list) list = fun s stk ->
  let nb_args = List.length stk in
  let rec eval_args n stk =
    match (n, stk) with
    | (0, stk   ) -> stk
    | (_, []    ) -> assert false
    | (n, u::stk) -> let (u,s) = whnf_stk u [] in
                     add_args u s :: eval_args (n-1) stk
  in
  let max_req acc r = if r.arity <= nb_args then max r.arity acc else acc in
  let n = List.fold_left max_req 0 s.def_rules in
  let stk = eval_args n stk in
  let match_rule acc r =
    (* First check that we have enough arguments. *)
    if r.arity > nb_args then acc else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let new_pvar i = ITag(i) in
    let uvars = Array.init (Bindlib.mbinder_arity r.lhs) new_pvar in
    let lhs = Bindlib.msubst r.lhs uvars in
    if !debug_eval then log "eval" "RULE trying rule [%a]" pp_rule (s,r);
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args lhs stk =
      match (lhs, stk) with
      | ([]    , stk   ) ->
          (Bindlib.msubst r.rhs (Array.map unfold uvars), stk) :: acc
      | (t::lhs, v::stk) ->
          if matching uvars t v then match_args lhs stk else acc
      | (_     , _     ) -> assert false
    in
    match_args lhs stk
  in
  List.fold_left match_rule [] s.def_rules

and matching ar pat t =
  let t = unfold t in
  if !debug_eval then log "matc" "[%a] =~= [%a]" pp pat pp t;
  let res =
    match (pat, t) with
    | (Prod(_,a1,b1), Prod(_,a2,b2)) ->
        let (_,b1,b2) = Bindlib.unbind2 mkfree b1 b2 in
        matching ar a1 a2 && matching ar b1 b2
    | (Abst(_,_,t1) , Abst(_,_,t2) ) ->
        let (_,t1,t2) = Bindlib.unbind2 mkfree t1 t2 in
        matching ar t1 t2
    | (Appl(_,t1,u1), Appl(_,t2,u2)) -> matching ar t1 t2 && matching ar u1 u2
    | (Unif(_,_)    , _            ) -> assert false
    | (_            , Unif(_,_)    ) -> assert false
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Vari(x1)     , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Symb(s1)     , Symb(s2)     ) -> s1 == s2
    | (ITag(i)      , _            ) ->
        if ar.(i) = ITag(i) then (ar.(i) <- t; true) else eq_modulo ar.(i) t
    | (_            , _            ) -> false
  in
  if !debug_eval then log "matc" (r_or_g res "[%a] =~= [%a]") pp pat pp t; res

and eq_modulo : term -> term -> bool = fun a b ->
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
          | (a::la, b::lb) -> sync ((a,b)::acc) la lb
          | (la   , []   ) -> (add_args a (List.rev la), b, acc)
          | ([]   , lb   ) -> (a, add_args b (List.rev lb), acc)
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
        | (a            , b            ) -> add_constraint a b && eq_modulo l
  in
  let res = eq_modulo [(a,b)] in
  if !debug_equa then log "equa" (r_or_g res "%a == %a") pp a pp b; res  

(* [eval t] returns a weak head normal form of [t].  Note that some  arguments
   are evaluated if they might be used to allow the application of a rewriting
   rule. As their evaluation is kept, so this function does more normalisation
   that the usual weak head normalisation. *)
let eval : term -> term = fun t ->
  if !debug_eval then log "eval" "evaluating %a" pp t;
  let (u, stk) = whnf_stk t [] in
  let u = add_args u stk in
  if !debug_eval then log "eval" "produced %a" pp u; u
