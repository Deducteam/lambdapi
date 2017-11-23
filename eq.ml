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
