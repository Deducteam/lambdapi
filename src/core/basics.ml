(** Basic operations on terms. *)

open Extra
open Timed
open Terms

(** Sets and maps of variables. *)
module Var =
  struct
    type t = term Bindlib.var
    let compare = Bindlib.compare_vars
  end

module VarSet = Set.Make(Var)
module VarMap = Map.Make(Var)

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

(** [imply t u] creates the term [t ⇒ u], that is, the dependent product
    [∀x: t, u] where [u] does not depend on [x]. *)
let imply : term -> term -> term = fun t u ->
  let dummy = Bindlib.new_var mkfree "_" in
  Prod(t, Bindlib.unbox (Bindlib.bind_var dummy (lift u)))

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

(** [eq t u] tests the equality of [t] and [u] (up to α-equivalence). It fails
    if [t] or [u] contain terms of the form [Patt(i,s,e)] or [TEnv(te,e)].  In
    the process, subterms of the form [TRef(r)] in [t] and [u] may be set with
    the corresponding value to enforce equality. In other words,  [eq t u] can
    be used to implement non-linear matching (see {!module:Rewrite}). When the
    matching feature is used, one should make sure that [TRef] constructors do
    not appear both in [t] and in [u] at the same time. Indeed, the references
    are set naively, without checking occurence. *)
let eq : term -> term -> bool = fun a b -> a == b ||
  let exception Not_equal in
  let rec eq l =
    match l with
    | []       -> ()
    | (a,b)::l ->
    match (unfold a, unfold b) with
    | (a          , b          ) when a == b -> eq l
    | (Vari(x1)   , Vari(x2)   ) when Bindlib.eq_vars x1 x2 -> eq l
    | (Type       , Type       )
    | (Kind       , Kind       ) -> eq l
    | (Symb(s1,_) , Symb(s2,_) ) when s1 == s2 -> eq l
    | (Prod(a1,b1), Prod(a2,b2))
    | (Abst(a1,b1), Abst(a2,b2)) -> let (_, b1, b2) = Bindlib.unbind2 b1 b2 in
                                    eq ((a1,a2)::(b1,b2)::l)
    | (LLet(t1,a1,u1), LLet(t2,a2,u2)) ->
        let (_, u1, u2) = Bindlib.unbind2 u1 u2 in
        eq ((a1,a2)::(t1,t2)::(u1,u2)::l)
    | (Appl(t1,u1), Appl(t2,u2)) -> eq ((t1,t2)::(u1,u2)::l)
    | (Meta(m1,e1), Meta(m2,e2)) when m1 == m2 ->
        eq (if e1 == e2 then l else List.add_array2 e1 e2 l)
    | (Wild       , _          )
    | (_          , Wild       ) -> eq l
    | (TRef(r)    , b          ) -> r := Some(b); eq l
    | (a          , TRef(r)    ) -> r := Some(a); eq l
    | (Patt(_,_,_), _          )
    | (_          , Patt(_,_,_))
    | (TEnv(_,_)  , _          )
    | (_          , TEnv(_,_)  ) -> assert false
    | (_          , _          ) -> raise Not_equal
  in
  try eq [(a,b)]; true with Not_equal -> false

(** [eq_vari t u] checks that [t] and [u] are both variables, and the they are
    pariwise equal. *)
let eq_vari : term -> term -> bool = fun t u ->
  match (unfold t, unfold u) with
  | (Vari(x), Vari(y)) -> Bindlib.eq_vars x y
  | (_      , _      ) -> false

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
let is_symb : sym -> term -> bool = fun s t ->
  match unfold t with
  | Symb(r,_) -> r == s
  | _         -> false

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
    | LLet(t,a,u) -> iter t; iter a; iter (Bindlib.subst u Kind)
  in iter

(** {3 Contexts} *)

(** [ctx_unbind ctx a def b] returns the triple [(x,b,ctx')] such that [(x,b)]
    is the unbinding of [b] and [ctx'] is the context [ctx] extended with, if
    [x] occurs in [b]
    - the assumption that [x] is of type [a] if [def] is [None], and
    - the definition of [x] in [def] of type [a] otherwise. *)
let ctx_unbind : ctxt -> term -> term option -> tbinder ->
  tvar * term * ctxt = fun ctx a def b ->
  let (x, t) = Bindlib.unbind b in
  (x, t, if Bindlib.binder_occur b then (x, a, def) :: ctx else ctx)

(** [type_of x ctx] returns the type of [x] in the context [ctx] when it
    appears, and raises [Not_found] otherwise. *)
let type_of : tvar -> ctxt -> term = fun x ctx ->
  let (_,a,_) = List.find (fun (y,_,_) -> Bindlib.eq_vars x y) ctx in a

(** [def_of x ctx] returns the definition of [x] in the context [ctx] if it
    appears, and [None] otherwise *)
let rec def_of : tvar -> ctxt -> term option = fun x ctx ->
  match ctx with
  | []         -> None
  | (y,_,d)::l -> if Bindlib.eq_vars x y then d else def_of x l

(** [ctx_mem x ctx] tells whether variable [x] is mapped in the context
    [ctx]. *)
let ctx_mem : tvar -> ctxt -> bool = fun x ->
  List.exists (fun (y,_,_) -> Bindlib.eq_vars x y)

(** [prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. It returns the number of products as well. *)
let prod : ctxt -> term -> term * int = fun ctx t ->
  let fn (t,c) elt =
    match elt with
    | (x,a,None   ) -> (_Prod (lift a) (Bindlib.bind_var x t), c + 1)
    | (x,a,Some(u)) -> (_LLet (lift u) (lift a) (Bindlib.bind_var x t), c)
  in
  let t, c = List.fold_left fn (lift t, 0) ctx in
  (Bindlib.unbox t, c)

(** [make_meta ctx a] creates a metavariable of type [a],  with an environment
    containing the variables of context [ctx]. *)
let make_meta : ctxt -> term -> term = fun ctx a ->
  let prd, len = prod ctx a in
  let m = fresh_meta prd len in
  let get_var (x,_,_) = Vari(x) in
  Meta(m, Array.of_list (List.rev_map get_var ctx))

(** [subctx ctx vs] return the sub-context of [ctx] made of the variables of
    [vs]. *)
let subctx : ctxt -> tvar array -> ctxt = fun ctx vs ->
  let f ((x,_,_) as hyp) ctx =
    if Array.exists (Bindlib.eq_vars x) vs then hyp::ctx else ctx
  in
  List.fold_right f ctx []

(** {3 Metavariables} *)

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
    | LLet(t,a,u) -> iter t; iter a; iter (Bindlib.subst u Kind)
  in iter

(** [occurs m t] tests whether the metavariable [m] occurs in the term [t]. *)
let occurs : meta -> term -> bool =
  let exception Found in fun m t ->
  let fn p = if m == p then raise Found in
  try iter_meta false fn t; false with Found -> true

(** [get_metas b t] returns the list of all the metavariables in [t], and in
   the types of metavariables recursively if [b], sorted wrt [cmp_meta]. *)
let get_metas : bool -> term -> meta list = fun b t ->
  let open Pervasives in
  let l = ref [] in
  iter_meta b (fun m -> l := m :: !l) t;
  List.sort_uniq cmp_meta !l

(** [has_metas b t] checks whether there are metavariables in [t], and in the
   types of metavariables recursively if [b] is true. *)
let has_metas : bool -> term -> bool =
  let exception Found in fun b t ->
  try iter_meta b (fun _ -> raise Found) t; false with Found -> true

(** [distinct_vars ts] checks that [ts] is made of distinct
   variables and returns these variables. *)
let distinct_vars : ctxt -> term array -> tvar array option =
  let exception Not_unique_var in fun ctx ts ->
  let open Pervasives in
  let vars = ref VarSet.empty in
  let to_var t =
    match unfold t with
    | Vari(x) ->
        let x =
          (* If variable is defined in [ctx], replace the var by its
             definition. *)
          match def_of x ctx with
          | Some(Vari(x)) -> x
          | None          -> x
          | Some(_)       -> raise Not_unique_var
        in
        if not (VarSet.mem x !vars) then (vars := VarSet.add x !vars; x) else
        raise Not_unique_var
    | _       -> raise Not_unique_var
  in try Some (Array.map to_var ts) with Not_unique_var -> None

(** {3 Conversion of a rule into a "pair" of terms} *)

(** [terms_of_rule r] converts the RHS (right hand side) of the rewriting rule
    [r] into a term.  The bound higher-order variables of the original RHS are
    substituted using [Patt] constructors.  They are thus represented as their
    LHS counterparts. This is a more convenient way of representing terms when
    analysing confluence or termination. *)
let term_of_rhs : rule -> term = fun r ->
  let fn i (name, arity) =
    let make_var i = Bindlib.new_var mkfree (Printf.sprintf "x%i" i) in
    let vars = Array.init arity make_var in
    let p = _Patt (Some(i)) name (Array.map Bindlib.box_var vars) in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar vars p))
  in
  Bindlib.msubst r.rhs (Array.mapi fn r.vars)
