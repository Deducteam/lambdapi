(** Basic operations on terms. *)

open Timed
open Term
open Lplib.Extra

(** [to_tvar t] returns [x] if [t] is of the form [Vari x] and fails
    otherwise. *)
let to_tvar : term -> tvar = fun t ->
  match t with Vari(x) -> x | _ -> assert false

(** {b NOTE} the {!val:Array.map to_tvar} function is useful when working
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

(** [iter f t] applies the function [f] to every node of the term [t] with
   bound variables replaced by [Kind]. Note: [f] is called on already unfolded
   terms only. *)
let iter : (term -> unit) -> term -> unit = fun action ->
  let rec iter t =
    let t = unfold t in
    action t;
    match t with
    | Wild
    | TRef(_)
    | Vari(_)
    | Type
    | Kind
    | Symb(_)     -> ()
    | Patt(_,_,ts)
    | TEnv(_,ts)
    | Meta(_,ts)  -> Array.iter iter ts
    | Prod(a,b)
    | Abst(a,b)   -> iter a; iter (Bindlib.subst b mk_Kind)
    | Appl(t,u)   -> iter t; iter u
    | LLet(a,t,u) -> iter a; iter t; iter (Bindlib.subst u mk_Kind)
  in iter

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

(** Functions to manipulate metavariables. This module includes
    {!module:Term.Meta}. *)
module Meta = struct
  include Meta

  (** [make ctx a] creates a fresh metavariable term of type [a] in the
      context [ctx]. *)
  let make : ctxt -> term -> term = fun ctx a ->
    let prd, len = Ctxt.to_prod ctx a in
    let m = Meta.fresh prd len in
    let get_var (x,_,_) = mk_Vari(x) in
    mk_Meta(m, Array.of_list (List.rev_map get_var ctx))

  (** [make_codomain ctx a] creates a fresh metavariable term [b] of type
      [Type] in the context [ctx] extended with a fresh variable of type
      [a]. *)
  let make_codomain : ctxt -> term -> tbinder = fun ctx a ->
    let x = new_tvar "x" in
    let b = make ((x, a, None) :: ctx) mk_Type in
    Bindlib.unbox (Bindlib.bind_var x (lift b))
  (* Possible improvement: avoid lift by defining a function _Meta.make
     returning a tbox. *)

  (** [iter b f t] applies the function [f] to every metavariable of [t], and
      to the type of every metavariable recursively if [b] is true. *)
  let iter : bool -> (t -> unit) -> term -> unit = fun b f ->
    let rec iter t =
      match unfold t with
      | Patt(_,_,_)
      | TEnv(_,_)
      | Wild
      | TRef(_)
      | Vari(_)
      | Type
      | Kind
      | Symb(_)     -> ()
      | Prod(a,b)
      | Abst(a,b)   -> iter a; iter (Bindlib.subst b mk_Kind)
      | Appl(t,u)   -> iter t; iter u
      | Meta(v,ts)  -> f v; Array.iter iter ts; if b then iter !(v.meta_type)
      | LLet(a,t,u) -> iter a; iter t; iter (Bindlib.subst u mk_Kind)
    in iter

  (** [occurs m t] tests whether the metavariable [m] occurs in the term
      [t]. *)
  let occurs : t -> term -> bool =
    let exception Found in fun m t ->
    let fn p = if m == p then raise Found in
    try iter false fn t; false with Found -> true

  (** [add b t ms] extends [ms] with all the metavariables of [t], and
      those in the types of these metavariables recursively if [b]. *)
  let add : bool -> term -> MetaSet.t -> MetaSet.t = fun b t ms ->
    let open Stdlib in
    let ms = ref ms in
    iter b (fun m -> ms := MetaSet.add m !ms) t;
    !ms

  (** [get b t] returns the set of all the metavariables in [t], and in
      the types of metavariables recursively if [b]. *)
  let get : bool -> term -> MetaSet.t = fun b t ->
    add b t MetaSet.empty

  (** [has b t] checks whether there are metavariables in [t], and in
      the types of metavariables recursively if [b] is true. *)
  let has : bool -> term -> bool =
    let exception Found in fun b t ->
    try iter b (fun _ -> raise Found) t; false with Found -> true

end

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
    let p = _Patt (Some(i)) name (Array.map Bindlib.box_var vars) in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar vars p))
  in
  Bindlib.msubst r.rhs (Array.mapi fn r.vars)
