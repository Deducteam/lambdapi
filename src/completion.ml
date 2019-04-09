(** Completion procedure *)

open Terms
open Basics
open Extra

(** total strict order *)
type 'a order = 'a -> 'a -> bool

let gt : 'a order -> 'a -> 'a -> bool = fun ord a b -> ord a b

(** [ge ord] calculates the reflexive closure of [ord] *)
let ge : 'a order -> 'a -> 'a -> bool = fun ord a b -> a = b || ord a b

(** [ord_lex ord] calculates the lexicographic order corresponding to the
    alphabetical order [ord] *)
let ord_lex : 'a order -> ('a list) order = fun ord l1 l2 ->
  let rec elim_comm l1 l2 = match (l1, l2) with
    | h1 :: t1, h2 :: t2 -> begin match ord h1 h2 with
        | false -> if h1 = h2 then elim_comm t1 t2 else assert false
        | _     -> l1, l2
      end
    | _                  -> l1, l2 in
  match elim_comm l1 l2 with
  | [], _              -> false
  | _, []              -> true
  | h1 :: _, h2 :: _ -> ord h1 h2

let get_sym : term -> sym = fun t -> match unfold t with
  | Symb (s, _) -> s
  | _          -> assert false

(** [lpo ord] calculates the lexicographic path ordering corresponding to
    the strict total order [ord] on the set of all function symbols *)
let rec lpo : sym order -> term order = fun ord t1 t2 ->
  let f, args = get_args t1 in
  let f = get_sym f in
  if List.exists (fun x -> ge (lpo ord) x t2) args then true
  else
    let g, args' = get_args t2 in
    let g = get_sym g in
    match ord f g with
    | true  ->
        if List.for_all (fun x -> gt (lpo ord) t1 x) args' then true
        else
          false
    | false ->
        if f = g then
          List.for_all (fun x -> gt (lpo ord) t1 x) args' &&
          ord_lex (lpo ord) args args'
        else false

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

type rule_ = sym * pp_hint * rule

(** [cp builtins r1 r2] calculates the critical pairs of the rules r1 and r2
    *)
let cp : sym StrMap.t -> rule_ -> rule_ -> (term * term) list
  = fun builtins (s1, h1, r1) (s2, h2, r2) ->
  let arity1 = Bindlib.mbinder_arity r1.rhs in
  let arity2 = Bindlib.mbinder_arity r2.rhs in
  let cps = ref [] in
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
    | _              -> assert false in
  let metas1 = Array.init arity1 (fun _ -> None) in
  let lhs1 = List.map (fun p -> Bindlib.unbox (to_m 0 metas1 p)) r1.lhs in
  let lhs1 = Basics.add_args (Symb (s1, h1)) lhs1 in
  let find_cp : term -> unit = fun t ->
    let metas1 = Array.init arity1 (fun _ -> None) in
    let metas2 = Array.init arity2 (fun _ -> None) in
    let lhs2 = List.map (fun p -> Bindlib.unbox (to_m 0 metas2 p)) r2.lhs in
    let lhs2 = Basics.add_args (Symb (s2, h2)) lhs2 in
    let fn m =
      let m = match m with Some m -> m | None -> assert false in
      let xs = Array.init m.meta_arity (Printf.sprintf "x%i") in
      let xs = Bindlib.new_mvar mkfree xs in
      let e = Array.map _Vari xs in
      TE_Some (Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m e)))
    in
    let te_envs1 = Array.map fn metas1 in
    let te_envs2 = Array.map fn metas2 in
    let rhs1 = Bindlib.msubst r1.rhs te_envs1 in
    let rhs2 = Bindlib.msubst r2.rhs te_envs2 in
    let to_solve = [(t, lhs2)] in
    match Unif.(solve builtins false {no_problems with to_solve}) with
    | None    -> ()
    | Some cs ->
        if cs <> [] then () else cps := (rhs1, rhs2) :: !cps in
  Basics.iter find_cp lhs1; (* This only works for algebraic LHS *)
  !cps

(** [critical_pairs builtins rs] calculates the list of all critical pairs
    of the rewrite system rs *)
let rec critical_pairs : sym StrMap.t -> rule_ list -> (term * term) list
  = fun builtins rs ->
  match rs with
  | [] -> []
  | r :: rs' ->
      let cps = critical_pairs builtins rs in
      List.fold_left
        (fun acc r' ->
           cp builtins r r' @ cp builtins r' r @ acc)
           (cp builtins r r @ cps) rs'
