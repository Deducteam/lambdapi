(** Basic operations on terms. *)

open Extra
open Timed
open Terms

(** [fresh_vars n] creates an array of [n] fresh variables. The names of these
    variables is ["_var_i"], where [i] is a number introduced by the [Bindlib]
    library to avoid name clashes (minimal renaming is done). *)
let fresh_vars : int -> tvar array = fun n ->
  Bindlib.new_mvar mkfree (Array.make n "_var_")

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

(** [count_products a] returns the number of consecutive products at the  head
    of the term [a]. *)
let rec count_products : term -> int = fun t ->
  match unfold t with
  | Prod(_,b) -> 1 + count_products (Bindlib.subst b Kind)
  | _         -> 0

(** [get_args t] decomposes the {!type:term} [t] into a pair [(h,args)], where
    [h] is the head term of [t] and [args] is the list of arguments applied to
    [h] in [t]. The returned [h] cannot be an [Appl] node. *)
let get_args : term -> term * term list = fun t ->
  let rec get_args acc t =
    match unfold t with
    | Appl(t,u) -> get_args (u::acc) t
    | t         -> (t, acc)
  in get_args [] t

(** [get_args_len t] is similar to [get_args t] but it also returns the length
    of the list of arguments. *)
let get_args_len : term -> term * term list * int = fun t ->
  let rec get_args_len acc len t =
    match unfold t with
    | Appl(t, u) -> get_args_len (u::acc) (len + 1) t
    | t          -> (t, acc, len)
  in
  get_args_len [] 0 t

(** [add_args t args] builds the application of the {!type:term} [t] to a list
    arguments [args]. When [args] is empty, the returned value is (physically)
    equal to [t]. *)
let add_args : term -> term list -> term = fun t args ->
  let rec add_args t args =
    match args with
    | []      -> t
    | u::args -> add_args (Appl(t,u)) args
  in add_args t args

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
let is_symb : sym -> term -> bool = fun s t ->
  match unfold t with
  | Symb(r) -> r == s
  | _       -> false

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
    | Abst(a,b)   -> iter a; iter (Bindlib.subst b Kind)
    | Appl(t,u)   -> iter t; iter u
    | LLet(a,t,u) -> iter a; iter t; iter (Bindlib.subst u Kind)
  in iter

(** {3 Metavariables} *)

(** [make_meta ctx a] creates a metavariable of type [a],  with an environment
    containing the variables of context [ctx]. *)
let make_meta : ctxt -> term -> term = fun ctx a ->
  let prd, len = Ctxt.to_prod ctx a in
  let m = fresh_meta prd len in
  let get_var (x,_,_) = Vari(x) in
  Meta(m, Array.of_list (List.rev_map get_var ctx))

(** [iter_meta b f t] applies the function [f] to every metavariable of [t],
   and to the type of every metavariable recursively if [b] is true. *)
let iter_meta : bool -> (meta -> unit) -> term -> unit = fun b f ->
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
    | Abst(a,b)   -> iter a; iter (Bindlib.subst b Kind)
    | Appl(t,u)   -> iter t; iter u
    | Meta(v,ts)  -> f v; Array.iter iter ts; if b then iter !(v.meta_type)
    | LLet(a,t,u) -> iter a; iter t; iter (Bindlib.subst u Kind)
  in iter

(** [occurs m t] tests whether the metavariable [m] occurs in the term [t]. *)
let occurs : meta -> term -> bool =
  let exception Found in fun m t ->
  let fn p = if m == p then raise Found in
  try iter_meta false fn t; false with Found -> true

(** [add_metas b t ms] extends [ms] with all the metavariables of [t], and
   those in the types of these metavariables recursively if [b]. *)
let add_metas : bool -> term -> MetaSet.t -> MetaSet.t = fun b t ms ->
  let open Stdlib in
  let ms = ref ms in
  iter_meta b (fun m -> ms := MetaSet.add m !ms) t;
  !ms

(** [get_metas b t] returns the set of all the metavariables in [t], and in
    the types of metavariables recursively if [b]. *)
let get_metas : bool -> term -> MetaSet.t = fun b t ->
  add_metas b t MetaSet.empty

(** [has_metas b t] checks whether there are metavariables in [t], and in the
    types of metavariables recursively if [b] is true. *)
let has_metas : bool -> term -> bool =
  let exception Found in fun b t ->
  try iter_meta b (fun _ -> raise Found) t; false with Found -> true

(** [distinct_vars ctx ts]  checks  that terms of  [ts] are made of  variables
    that are themselves or their definition in  [ctx] (if it exists) distinct.
    If so, the variables are returned. *)
let distinct_vars : ctxt -> term array -> tvar array option = fun ctx ts ->
  let exception Not_unique_var in
  let open Stdlib in
  let vars = ref VarSet.empty in
  let to_var t =
    match Ctxt.unfold ctx t with
    | Vari(x) ->
        if VarSet.mem x !vars then raise Not_unique_var;
        vars := VarSet.add x !vars;
        x
    | _       -> raise Not_unique_var
  in
  try Some (Array.map to_var ts) with Not_unique_var -> None

(** {3 Conversion of a rule into a "pair" of terms} *)

(** [terms_of_rule r] converts the RHS (right hand side) of the rewriting rule
    [r] into a term.  The bound higher-order variables of the original RHS are
    substituted using [Patt] constructors.  They are thus represented as their
    LHS counterparts. This is a more convenient way of representing terms when
    analysing confluence or termination. *)
let term_of_rhs : rule -> term = fun r ->
  let fn i x =
    let (name, arity) = (Bindlib.name_of x, r.arities.(i)) in
    let make_var i = Bindlib.new_var mkfree (Printf.sprintf "x%i" i) in
    let vars = Array.init arity make_var in
    let p = _Patt (Some(i)) name (Array.map Bindlib.box_var vars) in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar vars p))
  in
  Bindlib.msubst r.rhs (Array.mapi fn r.vars)
