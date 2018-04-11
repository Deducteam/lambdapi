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

(** [split_args t1 t2] extracts the maximum possible number of arguments  from
    [t1] and [t2]. The triple that is returned contains the remaining parts of
    the terms (their heads) and the list of the arguments put into pairs. Note
    that one of the returned terms must not be an application. *)
let split_args : term -> term -> term * term * (term * term) list =
  let rec split args a b =
    match (unfold a, unfold b) with
    | (Appl(t1,u1), Appl(t2,u2)) -> split ((u1,u2)::args) t1 t2
    (* FIXME should we unify ?
    | (Meta(u1,e1), Meta(u2,e2)) when u1 == u2 -> (a,b,args)
    | (Meta(m,e)  , b          ) when instantiate m e b -> split args a b
    | (a          , Meta(m,e)  ) when instantiate m e a -> split args a b
    *)
    | (a          , b          ) -> (a,b,args)
  in split []

(** [unify_list l] tests equality between all the pairs of terms of [l], while
    possibly instantiating metavariables. *)
let rec unify_list : (term * term) list -> bool = fun l ->
  match l with
  | []                   -> true
  | (a,b)::l when a == b -> unify_list l
  | (a,b)::l             ->
      let (a,b,args) = split_args a b in
      match (a, b) with
      | (Wild         , _            ) -> assert false
      | (_            , Wild         ) -> assert false
      | (ITag(_)      , _            ) -> assert false
      | (_            , ITag(_)      ) -> assert false
      | (Appl(_,_)    , Appl(_,_)    ) -> assert false
      | (Type         , Type         ) -> assert(args = []); unify_list l
      | (Kind         , Kind         ) -> assert(args = []); unify_list l
      | (Symb(Sym(s1)), Symb(Sym(s2))) ->
          s1 == s2 &&
          unify_list (args @ l)
      | (Symb(Def(s1)), Symb(Def(s2))) ->
          s1 == s2 &&
          eq_list args &&
          unify_list l
      | (Vari(x1)     , Vari(x2)     ) ->
          Bindlib.eq_vars x1 x2 &&
          eq_list args &&
          unify_list l
      | (Prod(a1,b1)  , Prod(a2,b2)  ) ->
          assert(args = []);
          let (_,b1,b2) = Bindlib.unbind2 mkfree b1 b2 in
          unify_list ((a1,a2)::(b1,b2)::l)
      | (Abst(a1,t1)  , Abst(a2,t2)  ) ->
          (* NOTE [a] and [b] are not in WHNF, [args] can be non-empty. *)
          let (_,t1,t2) = Bindlib.unbind2 mkfree t1 t2 in
          eq_list args &&
          unify_list ((a1,a2)::(t1,t2)::l)
      | (Meta(u1,e1)  , Meta(u2,e2)  ) when u1 == u2 ->
          let args = ref args in
          Array.iter2 (fun a b -> args := (a,b)::!args) e1 e2;
          eq_list !args &&
          unify_list l
      (* FIXME if we prevent these unifications, many examples fail.
      | (Meta(m,e)    , Appl(_,_)    ) ->
          begin
            let (h,ts) = get_args b in
            match h with
            | Symb(Sym(s)) -> wrn "HERE1\n"; false
            | _            -> wrn "THERE\n"; false
          end
      | (Appl(_,_)    , Meta(m,e)    ) ->
          begin
            let (h,ts) = get_args a in
            match h with
            | Symb(Sym(s)) -> wrn "HERE2\n"; false
            | _            -> wrn "THERE\n"; false
          end
      *)
      | (Meta(u,e)    , b            ) when instantiate u e b -> unify_list l
      | (a            , Meta(u,e)    ) -> instantiate u e a && unify_list l
      | (_            , _            ) -> false

(** [unify t u] tests the equality of the two terms [t] and [u] while possibly
    instantiating metavariables. *)
let unify : term -> term -> bool = fun a b ->
  unify_list [(a,b)]

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
    | []                      -> true
    | (a,b)::l when unify a b -> unify_modulo l
    | (a,b)::l                ->
    let a = whnf a in
    let b = whnf b in
    let unif =
      match !constraints with
      | None -> (fun a b -> unify_modulo [(a,b)])
      | _    -> eq
    in
    let (a,b,args) = split_args a b in
    match (unfold a, unfold b) with
    | (Wild         , _            )
    | (_            , Wild         )
    | (ITag(_)      , _            )
    | (_            , ITag(_)      )
    | (Type         , Type         ) -> assert (args = []); unify_modulo l
    | (Kind         , Kind         ) -> assert (args = []); unify_modulo l
    | (Prod(a1,b1)  , Prod(a2,b2)  ) ->
        assert (args = []);
        let (_,b1,b2) = Bindlib.unbind2 mkfree b1 b2 in
        unify_modulo ((a1,a2)::(b1,b2)::l)
    | (Abst(a1,t1)  , Abst(a2,t2)  ) ->
        assert (args = []);
        let (_,t1,t2) = Bindlib.unbind2 mkfree t1 t2 in
        unify_modulo ((a1,a2)::(t1,t2)::l)
    | (Vari(x1)     , Vari(x2)     ) when Bindlib.eq_vars x1 x2 ->
        List.for_all (fun (a,b) -> unif a b || add_constraint a b) args &&
        unify_modulo l
    | (Symb(Sym(s1)), Symb(Sym(s2))) ->
        s1 == s2 && unify_modulo (args @ l)
    | (Symb(Def(s1)), Symb(Def(s2))) when s1 == s2 && args = [] ->
        unify_modulo l
    | (Meta(u1,e1)  , Meta(u2,e2)  ) ->
        u1 == u2 &&
        Array.for_all2 (fun a b -> unif a b || add_constraint a b) e1 e2 &&
        List.for_all (fun (a,b) -> unif a b || add_constraint a b) args &&
        unify_modulo l
    | (a            , b            ) ->
        match !constraints with
        | None ->
            unify a b &&
            (List.for_all (fun (a,b) -> unif a b) args) &&
            unify_modulo l
        | _    ->
            let a = add_args a (List.map fst args) in
            let b = add_args b (List.map snd args) in
            add_constraint a b && unify_modulo l
  in
  let res = unify_modulo [(a,b)] in
  if !debug_equa then log "unif" (r_or_g res "%a == %a") pp a pp b; res
