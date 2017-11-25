open Extra
open Console
open Terms
open Print

(* [occurs r t] checks whether the unification variable [r] occurs in [t]. *)
let rec occurs : unif -> term -> bool = fun r t ->
  match unfold t with
  | Prod(_,a,b) -> occurs r a || occurs r (Bindlib.subst b Kind)
  | Abst(_,a,t) -> occurs r a || occurs r (Bindlib.subst t Kind)
  | Appl(_,t,u) -> occurs r t || occurs r u
  | Unif(_,u,e) -> u == r || Array.exists (occurs r) e
  | Type        -> false
  | Kind        -> false
  | Vari(_)     -> false
  | Symb(_)     -> false
  | PVar(_)     -> assert false

(* NOTE: pattern variables prevent unification to ensure that they  cannot  be
   absorbed by unification varialbes (and do not escape rewriting code). *)

(* [unify r t] tries to unify [r] with [t],  and returns a boolean to indicate
   whether it succeeded or not. *)
let unify : unif -> term array -> term -> bool =
  fun r env a ->
    assert (!r = None);
    not (occurs r a) &&
      let to_var t = match t with Vari v -> v | _ -> assert false in
      let vars = Array.map to_var env in
      let b = Bindlib.bind_mvar vars (lift a) in
      assert (Bindlib.is_closed b);
      r := Some(Bindlib.unbox b); true

(* [eq t u] tests the equality of the terms [t] and [u]. Pattern variables may
   be instantiated in the process. *)
let eq : ?rewrite: bool -> term -> term -> bool = fun ?(rewrite=false) a b ->
  if !debug then log "equa" "%a =!= %a" pp a pp b;
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
    | (_            , PVar(_)      ) -> assert false
    | (PVar(r)      , b            ) -> assert rewrite; r := Some b; true
    | (Unif(_,r1,e1), Unif(_,r2,e2)) when r1 == r2 -> Array.for_all2 eq e1 e2
    | (Unif(_,r,e)  , b            ) -> unify r e b
    | (a            , Unif(_,r,e)  ) -> unify r e a
    | (_            , _            ) -> false
  in
  let res = eq a b in
  if !debug then log "equa" (r_or_g res "%a =!= %a") pp a pp b; res

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
    let new_pvar _ = PVar(ref None) in
    let uvars = Array.init (Bindlib.mbinder_arity r.lhs) new_pvar in
    let lhs = Bindlib.msubst r.lhs uvars in
    if !debug_eval then log "eval" "RULE trying rule [%a]" pp_rule (s,r);
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args lhs stk =
      match (lhs, stk) with
      | ([]    , stk   ) ->
          (Bindlib.msubst r.rhs (Array.map unfold uvars), stk) :: acc
      | (t::lhs, v::stk) ->
          if eq ~rewrite:true t v then match_args lhs stk else acc
      | (_     , _     ) -> assert false
    in
    match_args lhs stk
  in
  List.fold_left match_rule [] s.def_rules

(* [eval t] returns a weak head normal form of [t].  Note that some  arguments
   are evaluated if they might be used to allow the application of a rewriting
   rule. As their evaluation is kept, so this function does more normalisation
   that the usual weak head normalisation. *)
let eval : term -> term = fun t ->
  if !debug_eval then log "eval" "evaluating %a" pp t;
  let (u, stk) = whnf_stk t [] in
  let u = add_args u stk in
  if !debug_eval then log "eval" "produced %a" pp u; u

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

let eq_modulo : term -> term -> bool = fun a b ->
  if !debug then log "equa" "%a == %a" pp a pp b;
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
  if !debug then log "equa" (r_or_g res "%a == %a") pp a pp b; res  
