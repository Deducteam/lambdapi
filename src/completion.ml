(** Completion procedure for closed equations *)

open Terms
open Basics
open Extra
open Timed

type 'a cmp = 'a -> 'a -> int

(** [ord_lex ord] computes the lexicographic order corresponding to the
    alphabetical order [ord] *)
let rec ord_lex : 'a cmp -> 'a list cmp = fun ord l1 l2 ->
  match (l1, l2) with
  | [], []             -> 0
  | [], _              -> -1
  | _, []              -> 1
  | h1 :: t1, h2 :: t2 ->
      match ord h1 h2 with
      | 0 -> ord_lex ord t1 t2
      | x -> x

let get_sym : term -> sym = fun t -> match unfold t with
  | Symb (s, _) -> s
  | _           -> assert false

(** [lpo ord] computes the lexicographic path ordering corresponding to
    the strict total order [ord] on the set of all function symbols *)
let rec lpo : sym cmp -> term cmp = fun ord t1 t2 ->
  let f, args = get_args t1 in
  let f = get_sym f in
  if List.exists (fun x -> lpo ord x t2 >= 0) args then 1
  else
    let g, args' = get_args t2 in
    let g = get_sym g in
    match ord f g with
    | 1 ->
        if List.for_all (fun x -> lpo ord t1 x > 0) args' then 1
        else -1
    | 0 ->
        if List.for_all (fun x -> lpo ord t1 x > 0) args' then
          ord_lex (lpo ord) args args'
        else -1
    | _ -> -1

(** [build_meta_type k] builds the type “∀(x₁:A₁) (x₂:A₂) ⋯ (xk:Ak), B” where
    “x₁” through “xk” are fresh variables, “Ai = Mi[x₁,⋯,x(i-1)]”, “Mi” is a
    new metavar of arity “i-1” and type “∀(x₁:A₂) ⋯ (x(i-1):A(i-1), TYPE”. *)
let build_meta_type : int -> term = fun k ->
  assert (k>=0);
  let vs = Bindlib.new_mvar mkfree (Array.make k "x") in
  let rec build_prod k p =
    if k = 0 then p
    else
      let k = k-1 in
      let mk_typ = Bindlib.unbox (build_prod k _Type) in
      let mk = fresh_meta mk_typ k in
      let tk = _Meta mk (Array.map _Vari (Array.sub vs 0 k)) in
      let b = Bindlib.bind_var vs.(k) p in
      let p = Bindlib.box_apply2 (fun a b -> Prod(a,b)) tk b in
      build_prod k p
  in
  let mk_typ = Bindlib.unbox (build_prod k _Type) (*FIXME?*) in
  let mk = fresh_meta mk_typ k in
  let tk = _Meta mk (Array.map _Vari vs) in
  Bindlib.unbox (build_prod k tk)

type rule = sym * Terms.rule

(** [to_m k metas t] computes a new (boxed) term by replacing every pattern
    variable in [t] by a fresh meta-variable and store the latter in [metas],
    where [k] indicates the order of the term obtained *)
let rec to_m : int -> (meta option) array -> term -> tbox = fun k metas t ->
  match unfold t with
  | Vari x         -> _Vari x
  | Symb (s, h)    -> _Symb s h
  | Abst (a, t)    ->
      let (x, t) = Bindlib.unbind t in
      _Abst (to_m 0 metas a) (Bindlib.bind_var x (to_m 0 metas t))
  | Appl (t, u)    -> _Appl (to_m (k + 1) metas t) (to_m 0 metas u)
  | Patt (i, n, a) ->
      begin
        let a = Array.map (to_m 0 metas) a in
        let l = Array.length a in
        match i with
        | None   ->
            let m = fresh_meta ~name:n (build_meta_type (l + k)) l in
            _Meta m a
        | Some i ->
            match metas.(i) with
            | Some m -> _Meta m a
            | None   ->
                let m = fresh_meta ~name:n (build_meta_type (l + k)) l in
                metas.(i) <- Some m;
                _Meta m a
      end
  | _              -> assert false

(** [to_term r] translates the rule [r] into a pair of terms *)
let to_term : rule -> term * term = fun (s, r) ->
  let arity = Bindlib.mbinder_arity r.rhs in
  let metas = Array.init arity (fun _ -> None) in
  let lhs = List.map (fun p -> Bindlib.unbox (to_m 0 metas p)) r.lhs in
  let lhs = add_args (symb s) lhs in
  (* [to_term_env m] computes the term with environment correspoding to the
     meta-variable [m] *)
  let to_term_env : meta option -> term_env = fun m ->
    let m = match m with Some m -> m | None -> assert false in
    let xs = Array.init m.meta_arity (Printf.sprintf "x%i") in
    let xs = Bindlib.new_mvar mkfree xs in
    let ar = Array.map _Vari xs in
    TE_Some (Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m ar))) in
  let terms_env = Array.map to_term_env metas in
  let rhs = Bindlib.msubst r.rhs terms_env in
  (lhs, rhs)

(** First-order syntactic unification *)

exception Unsolvable

(** [unif_aux t1 t2 eqs] attempts to solve the first-order unification
    problem [(t1 = t2) :: eqs] *)
let rec unif_aux : term -> term -> unif_constrs -> unit = fun t1 t2 eqs ->
  match (t1, t2) with
  | Type, Type
  | Kind, Kind                    -> unif eqs
  | Symb(s1, _), Symb(s2, _)      ->
      if s1 == s2 then unif eqs else raise Unsolvable
  | Vari _, _
  | _, Vari _
  | Prod _, _
  | _, Prod _
  | Abst _, _
  | _, Abst _ -> assert false
  | Appl (t1, u1), Appl (t2, u2)  -> unif ((t1, t2) :: (u1, u2) :: eqs)
  | Meta (m1, ts1), Meta (_, ts2) ->
      assert (ts1 = [||] && ts2 = [||]);
      let vs = Bindlib.new_mvar mkfree [||] in
      let bt2 = Bindlib.bind_mvar vs (lift t2) in
      set_meta m1 (Bindlib.unbox bt2);
      unif eqs
  | (Meta (m1, ts1), t2)
  | (t2, Meta (m1, ts1))          ->
      if occurs m1 t2 then raise Unsolvable
      else
        assert (ts1 = [||]);
        let vs = Bindlib.new_mvar mkfree [||] in
        let bt2 = Bindlib.bind_mvar vs (lift t2) in
        set_meta m1 (Bindlib.unbox bt2);
        unif eqs
  | _                             -> raise Unsolvable

(** [unif eqs] attempts to solve the unification problem [eqs] *)
and unif : unif_constrs -> unit = fun eqs ->
  match eqs with
  | []              -> ()
  | (t1, t2) :: eqs -> unif_aux t1 t2 eqs

(** [cps rs] computes the critical pairs of the rewrite system [rs] *)
let cps : rule list -> (term * term) list = fun rs ->
  let acc = ref [] in
  let cps_aux : rule -> rule -> unit = fun r1 r2 ->
    let lhs1, rhs1 = to_term r1 in
    let lhs2, rhs2 = to_term r2 in
    let find_cp : term -> term -> unit = fun t1 t2 ->
      let reset_meta m = m.meta_value := None in
      iter_meta reset_meta lhs1;
      iter_meta reset_meta lhs2;
      try
        unif [(t1, t2)];
        acc := (rhs1, rhs2) :: !acc
      with Unsolvable -> () in
    let _, args1 = get_args lhs1 in
    let _, args2 = get_args lhs2 in
    find_cp lhs1 lhs2;
    List.iter (iter (find_cp lhs1)) args2;
    List.iter (iter (fun t -> find_cp t lhs2)) args1 in
  let rec cps rs =
    match rs with
    | []       -> ()
    | r :: rs' -> List.iter (cps_aux r) rs; cps rs' in
  cps rs;
  !acc
