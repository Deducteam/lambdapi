(** Basic operations on terms. *)

open Term
open Lplib open Extra

(** [to_tvar t] returns [x] if [t] is of the form [Vari x] and fails
    otherwise. *)
let to_tvar : term -> tvar = fun t ->
  match t with Vari(x) -> x | _ -> assert false

(** {b NOTE} the [Array.map to_tvar] function is useful when working
   with multiple binders. For example, this is the case when manipulating
   pattern variables ([Patt] constructor) or metatavariables ([Meta]
   constructor).  Remark that it is important for these constructors to hold
   an array of terms, rather than an array of variables: a variable can only
   be substituted when if it is injected in a term (using the [Vari]
   constructor). *)

(** {b NOTE} the result of {!val:to_tvar} can generally NOT be precomputed. A
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

(** General iterator on {b unfolded} terms. For each constructor
    [C] which takes arguments [a1], ..., [an] of the {!term} type, a
    function [do_c] which takes as many arguments as the constructor [C]
    (or [()] if the constructor is constant). For instance, to operate
    on all symbols of a term [t], [iter ~do_symb:(fun s -> ...) t]. *)
let iter
  ?(do_wild = ignore)
  ?(do_symb = ignore)
  ?(do_vari = ignore)
  ?(do_Type = ignore)
  ?(do_Kind = ignore)
  ?(do_patt = fun _ _ _ -> ())
  ?(do_plac = fun _ -> ())
  ?(do_meta = fun _ _ -> ())
  ?(do_appl = fun _ _ -> ())
  ?(do_abst = fun _ _ -> ())
  ?(do_prod = fun _ _ -> ())
  ?(do_llet = fun _ _ _ -> ()) =
  let rec iter t =
    match unfold t with
    | TRef _ -> assert false (* should not appear in unfolded terms *)
    | TEnv _ -> assert false (* should not appear in unfolded terms *)
    | Wild -> do_wild ()
    | Type -> do_Type ()
    | Kind -> do_Kind ()
    | Symb s -> do_symb s
    | Vari x -> do_vari x
    | Plac b -> do_plac b
    | Patt (i,n,ts) ->
        do_patt i n ts;
        Array.iter iter ts
    | Meta (m,ts) ->
        do_meta m ts;
        Array.iter iter ts
    | Appl (t, u) ->
        do_appl t u;
        iter t;
        iter u
    | Abst(a,b) ->
        do_abst a b;
        iter a;
        iter (snd (Bindlib.unbind b))
    | Prod(a,b) ->
        do_prod a b;
        iter a;
        iter (snd (Bindlib.unbind b))
    | LLet(a,t,u) ->
        do_llet a t u;
        iter a;
        iter t;
        iter (snd (Bindlib.unbind u))
  in
  iter

(** [unbind_name b s] is like [Bindlib.unbind b] but returns a valid variable
    name when [b] binds no variable. The string [s] is the prefix of the
    variable's name.*)
let unbind_name : string -> tbinder -> tvar * term = fun s b ->
  if Bindlib.binder_occur b then Bindlib.unbind b
  else let x = new_tvar s in (x, Bindlib.subst b (mk_Vari x))

(** [unbind2_name b1 b2 s] is like [Bindlib.unbind2 b1 b2] but returns a valid
   variable name when [b1] or [b2] binds no variable. The string [s] is the
   prefix of the variable's name.*)
let unbind2_name : string -> tbinder -> tbinder -> tvar * term * term =
  fun s b1 b2 ->
  if Bindlib.binder_occur b1 || Bindlib.binder_occur b2 then
    Bindlib.unbind2 b1 b2
  else let x = new_tvar s in
       (x, Bindlib.subst b1 (mk_Vari x), Bindlib.subst b2 (mk_Vari x))

(** [distinct_vars ctx ts] checks that the terms [ts] are distinct
   variables. If so, the variables are returned. *)
let distinct_vars : ctxt -> term array -> tvar array option = fun ctx ts ->
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
   only, then [nl_distinct_vars ctx ts] returns [None]. Otherwise, it returns
   a pair [(vs, map)] where [vs] is an array of variables made of the linear
   variables of [ts] and fresh variables for the non-linear variables and the
   symbols prefixed by ['$'], and [map] records by which variable each linear
   symbol prefixed by ['$'] is replaced.

   Variables defined in [ctx] are unfolded.

   The symbols prefixed by ['$'] are introduced by [infer.ml] which converts
   metavariables into fresh symbols, and those metavariables are introduced by
   [sr.ml] which replaces pattern variables by metavariables. *)
let nl_distinct_vars
    : ctxt -> term array -> (tvar array * tvar StrMap.t) option =
  fun ctx ts ->
  let exception Not_a_var in
  let open Stdlib in
  let vars = ref VarSet.empty (* variables already seen (linear or not) *)
  and nl_vars = ref VarSet.empty (* variables occurring more then once *)
  and patt_vars = ref StrMap.empty in
  (* map from pattern variables to actual Bindlib variables *)
  let rec to_var t =
    match Ctxt.unfold ctx t with
    | Vari(v) ->
        if VarSet.mem v !vars then nl_vars := VarSet.add v !nl_vars
        else vars := VarSet.add v !vars;
        v
    | Symb(f) when f.sym_name <> "" && f.sym_name.[0] = '$' ->
        (* Symbols replacing pattern variables are considered as variables. *)
        let v =
          try StrMap.find f.sym_name !patt_vars
          with Not_found ->
            let v = new_tvar f.sym_name in
            patt_vars := StrMap.add f.sym_name v !patt_vars;
            v
        in to_var (mk_Vari v)
    | _ -> raise Not_a_var
  in
  let replace_nl_var v =
    if VarSet.mem v !nl_vars then new_tvar "_" else v
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
let sym_to_var : tvar StrMap.t -> term -> term = fun map ->
  let rec to_var t =
    match unfold t with
    | Symb f -> (try mk_Vari (StrMap.find f.sym_name map) with Not_found -> t)
    | Prod(a,b) -> mk_Prod (to_var a, to_var_binder b)
    | Abst(a,b) -> mk_Abst (to_var a, to_var_binder b)
    | LLet(a,t,u) -> mk_LLet (to_var a, to_var t, to_var_binder u)
    | Appl(a,b)  -> mk_Appl(to_var a, to_var b)
    | Meta(m,ts) -> mk_Meta(m, Array.map to_var ts)
    | Patt _ -> assert false
    | TEnv _ -> assert false
    | TRef _ -> assert false
    | _ -> t
  and to_var_binder b =
    let (x,b) = Bindlib.unbind b in
    Bindlib.unbox (Bindlib.bind_var x (lift (to_var b)))
  in fun t -> if StrMap.is_empty map then t else to_var t

(** [term_of_rhs r] converts the RHS (right hand side) of the rewriting rule
    [r] into a term. The bound higher-order variables of the original RHS are
    substituted using [Patt] constructors. They are thus represented as their
    LHS counterparts. This is a more convenient way of representing terms when
    analysing confluence or termination. *)
let term_of_rhs : rule -> term = fun r ->
  let fn i x =
    let (name, arity) = (Bindlib.name_of x, r.arities.(i)) in
    let vars = Array.init arity (new_tvar_ind "x") in
    let p = _Patt (Some i) name (Array.map _Vari vars) in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar vars p))
  in
  Bindlib.msubst r.rhs (Array.mapi fn r.vars)
