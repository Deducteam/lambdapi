(** Basic operations on terms. *)

open Term
open Lplib open Extra

(** [is_kind t] tells whether [t] is of the form Π x1, .., Π xn, TYPE. *)
let rec is_kind : term -> bool = fun t ->
  match unfold t with
  | Type -> true
  | Prod(_,b) -> is_kind (subst b mk_Kind)
  | _ -> false

(** [to_var t] returns [x] if [t] is of the form [Vari x] and fails
    otherwise. *)
let to_var : term -> var = fun t ->
  match t with Vari(x) -> x | _ -> assert false

(** {b NOTE} the [Array.map to_var] function is useful when working
   with multiple binders. For example, this is the case when manipulating
   pattern variables ([Patt] constructor) or metatavariables ([Meta]
   constructor).  Remark that it is important for these constructors to hold
   an array of terms, rather than an array of variables: a variable can only
   be substituted when if it is injected in a term (using the [Vari]
   constructor). *)

(** {b NOTE} the result of {!val:to_var} can generally NOT be precomputed. A
    first reason is that we cannot know in advance what variable identifier is
    going to arise when working under binders,  for which fresh variables will
    often be generated. A second reason is that free variables should never be
    “marshaled” (e.g., by the {!module:Sign} module), as this would break the
    freshness invariant of new variables. *)

(** Given a symbol [s], [remove_impl_args s ts] returns the non-implicit
   arguments of [s] among [ts]. *)
let remove_impl_args : sym -> term list -> term list = fun s ts ->
  let rec remove bs ts =
    match (bs, ts) with
    | (true::bs , _::ts) -> remove bs ts
    | (false::bs, t::ts) -> t :: remove bs ts
    | (_        , _    ) -> ts
  in
  remove s.sym_impl ts

(** [iter f t] applies the function [f] to every node of the term [t] with
   bound variables replaced by [Kind]. Note: [f] is called on already unfolded
   terms only. *)
let iter : (term -> unit) -> term -> unit = fun action ->
  let rec iter t =
    let t = unfold t in
    action t;
    match t with
    | Bvar _ -> assert false
    | Wild
    | Plac _
    | TRef(_)
    | Vari(_)
    | Type
    | Kind
    | Symb(_)     -> ()
    | Patt(_,_,ts)
    | Meta(_,ts)  -> Array.iter iter ts
    | Prod(a,b)
    | Abst(a,b)   -> iter a; iter (subst b mk_Kind)
    | Appl(t,u)   -> iter t; iter u
    | LLet(a,t,u) -> iter a; iter t; iter (subst u mk_Kind)
  in iter

(** [distinct_vars ctx ts] checks that the terms [ts] are distinct
   variables. If so, the variables are returned. *)
let distinct_vars : ctxt -> term array -> var array option = fun ctx ts ->
  let exception Not_unique_var in
  let open Stdlib in
  let vars = ref VarSet.empty in
  let to_var t =
    match Ctxt.unfold ctx t with
    | Vari(x) ->
        if VarSet.mem x !vars then raise Not_unique_var;
        vars := VarSet.add x !vars; x
    | _       -> raise Not_unique_var
  in
  try Some (Array.map to_var ts) with Not_unique_var -> None

(** If [ts] is not made of variables or function symbols prefixed by ['$']
   only, then [nl_distinct_vars ts] returns [None]. Otherwise, it returns
   a pair [(vs, map)] where [vs] is an array of variables made of the linear
   variables of [ts] and fresh variables for the non-linear variables and the
   symbols prefixed by ['$'], and [map] records by which variable each linear
   symbol prefixed by ['$'] is replaced.

   The symbols prefixed by ['$'] are introduced by [infer.ml] which converts
   metavariables into fresh symbols, and those metavariables are introduced by
   [sr.ml] which replaces pattern variables by metavariables. *)
let nl_distinct_vars : term array -> (var array * var StrMap.t) option =
  fun ts ->
  let exception Not_a_var in
  let open Stdlib in
  let vars = ref VarSet.empty (* variables already seen (linear or not) *)
  and nl_vars = ref VarSet.empty (* variables occurring more then once *)
  and patt_vars = ref StrMap.empty in
  (* map from pattern variables to actual variables *)
  let rec to_var t =
    match unfold t with
    | Vari(v) ->
        if VarSet.mem v !vars then nl_vars := VarSet.add v !nl_vars
        else vars := VarSet.add v !vars;
        v
    | Symb(f) when f.sym_name <> "" && f.sym_name.[0] = '$' ->
        (* Symbols replacing pattern variables are considered as variables. *)
        let v =
          try StrMap.find f.sym_name !patt_vars
          with Not_found ->
            let v = new_var f.sym_name in
            patt_vars := StrMap.add f.sym_name v !patt_vars;
            v
        in to_var (mk_Vari v)
    | _ -> raise Not_a_var
  in
  let replace_nl_var v =
    if VarSet.mem v !nl_vars then new_var "_" else v
  in
  try
    let vs = Array.map to_var ts in
    let vs = Array.map replace_nl_var vs in
    (* We remove non-linear variables from [!patt_vars] as well. *)
    let fn n v m = if VarSet.mem v !nl_vars then m else StrMap.add n v m in
    let map = StrMap.fold fn !patt_vars StrMap.empty in
    Some (vs, map)
  with Not_a_var -> None

(** [sym_to_var m t] replaces in [t] every symbol [f] by a variable according
   to the map [map]. *)
let sym_to_var : var StrMap.t -> term -> term = fun map ->
  let rec to_var t =
    match unfold t with
    | Symb f -> (try mk_Vari (StrMap.find f.sym_name map) with Not_found -> t)
    | Prod(a,b) -> mk_Prod (to_var a, to_var_binder b)
    | Abst(a,b) -> mk_Abst (to_var a, to_var_binder b)
    | LLet(a,t,u) -> mk_LLet (to_var a, to_var t, to_var_binder u)
    | Appl(a,b)  -> mk_Appl(to_var a, to_var b)
    | Meta(m,ts) -> mk_Meta(m, Array.map to_var ts)
    | Patt _ -> assert false
    | TRef _ -> assert false
    | _ -> t
  and to_var_binder b =
    let (x,b) = unbind b in bind_var x (to_var b)
  in fun t -> if StrMap.is_empty map then t else to_var t

(** [codom_binder n t] returns the [n]-th binder of [t] if [t] is a product of
    arith >= [n]. *)
let rec codom_binder : int -> term -> binder = fun n t ->
  match unfold t with
  | Prod(_,b) ->
      if n <= 0 then b else codom_binder (n-1) (subst b mk_Kind)
  | LLet(_,t,b) ->
      if n <= 0 then b else codom_binder (n-1) (subst b t)
  | _ -> assert false

(** [eq_alpha a b] tests the equality modulo alpha of [a] and [b]. *)
let rec eq_alpha a b =
  match unfold a, unfold b with
  | Vari x, Vari y -> Term.eq_vars x y
  | Type, Type
  | Kind, Kind -> true
  | Symb s1, Symb s2 -> s1==s2
  | Prod(a1,b1), Prod(a2,b2)
  | Abst(a1,b1), Abst(a2,b2) ->
      eq_alpha a1 a2 && let _,b1,b2 = Term.unbind2 b1 b2 in eq_alpha b1 b2
  | Appl(a1,b1), Appl(a2,b2) -> eq_alpha a1 a2 && eq_alpha b1 b2
  | Meta(m1,a1), Meta(m2,a2) -> m1 == m2 && Array.for_all2 eq_alpha a1 a2
  | LLet(a1,t1,u1), LLet(a2,t2,u2) ->
      eq_alpha a1 a2 && eq_alpha t1 t2
      && let _,u1,u2 = Term.unbind2 u1 u2 in eq_alpha u1 u2
  | Patt(Some i,_,ts), Patt(Some j,_,us) ->
      i=j && Array.for_all2 eq_alpha ts us
  | Patt(None,_,_), _ | _, Patt(None,_,_) -> assert false
  | TRef _, _| _, TRef _ -> assert false
  | _ -> false

(** [fold id t a] returns term binder [b] with binder name [id] such that
    [Bindlib.subst b t ≡ a]. *)
let fold (x:var) (t:term): term -> term =
  let rec aux u =
    if eq_alpha t u then mk_Vari x
    else
      match unfold u with
      | Appl(a,b) -> mk_Appl(aux a, aux b)
      | Abst(a,b) ->
          let x,b = Term.unbind b in mk_Abst(aux a, Term.bind_var x b)
      | Prod(a,b) ->
          let x,b = Term.unbind b in mk_Prod(aux a, Term.bind_var x b)
      | LLet(a,d,b) ->
          let x,b = Term.unbind b in mk_LLet(aux a, aux d, Term.bind_var x b)
      | Meta(m,us) -> mk_Meta(m,Array.map aux us)
      | _ -> u
  in
  aux
