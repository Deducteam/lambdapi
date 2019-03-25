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

(** [to_tvars ar] extracts an array of {!type:tvar} from an array of terms  of
    the form [Vari(x)].  The function (brutally) fails if any element of  [ar]
    does not correspond to a free variable. *)
let to_tvars : term array -> tvar array =
  Array.map (fun t -> match t with Vari(x) -> x | _ -> assert false)

(** {b NOTE} the {!val:to_tvars} function is useful when working with multiple
    binders. For example, this is the case when manipulating pattern variables
    ([Patt] constructor) or metatavariables ([Meta] constructor).  Remark that
    it is Importantly for these constructors to hold an array of terms, rather
    than an array of variables:  a variable can only be substituted when if it
    is injected in a term (using the [Vari] constructor). *)

(** {b NOTE} the result of {!val:to_tvars} can generally NOT be precomputed. A
    first reason is that we cannot know in advance what variable identifier is
    going to arise when working under binders,  for which fresh variables will
    often be generated. A second reason is that free variables should never be
    “marshalled” (e.g., by the {!module:Sign} module), as this would break the
    freshness invariant of new variables. *)

(** [count_products a] returns the number of consecutive products at the  head
    of the term [a]. *)
let rec count_products : term -> int = fun t ->
  match unfold t with
  | Prod(_,b) -> 1 + count_products (snd (Bindlib.unbind b))
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

(** [iter f t] applies the function [f] to every node of the term [t]. At each
    call, the function is given the list of the free variables in the term, in
    the reverse order they were given. Free variables that were already in the
    term before the call are not included in the list. *)
let iter : (tvar list -> term -> unit) -> term -> unit = fun action t ->
  let rec iter xs t =
    let t = unfold t in
    action xs t;
    match t with
    | Wild
    | TRef(_)
    | Vari(_)
    | Type
    | Kind
    | Symb(_)    -> ()
    | Patt(_,_,ts)
    | TEnv(_,ts)
    | Meta(_,ts) -> Array.iter (iter xs) ts
    | Prod(a,b)
    | Abst(a,b)  ->
       iter xs a;
       let (x,b') = Bindlib.unbind b in
       iter (if Bindlib.binder_occur b then x::xs else xs) b'
    | Appl(t,u)  -> iter xs t; iter xs u
  in
  iter [] (cleanup t)

(** [free_vars t] returns the set of free variables of [t]. *)
let free_vars : term -> VarSet.t =
  let open Pervasives in
  let vars = ref VarSet.empty in
  let action xs t =
    match t with
    | Vari x when not (List.exists (Bindlib.eq_vars x) xs) ->
       vars := VarSet.add x !vars
    | _ -> ()
  in
  fun t -> iter action t; !vars

(** [iter_meta f t] applies the function [f] to every metavariable in
   the term [t]. [t] must contain no [Patt], [TEnv], [Wild] or
   [TRef]. *)
let rec iter_meta : (meta -> unit) -> term -> unit = fun f t ->
  match unfold t with
  | Patt(_,_,_)
  | TEnv(_,_)
  | Wild
  | TRef(_)    -> assert false
  | Vari(_)
  | Type
  | Kind
  | Symb(_)    -> ()
  | Prod(a,b)
  | Abst(a,b)  -> iter_meta f a; iter_meta f (Bindlib.subst b Kind)
  | Appl(t,u)  -> iter_meta f t; iter_meta f u
  | Meta(v,ts) -> f v; iter_meta f !(v.meta_type); Array.iter (iter_meta f) ts

(** {b NOTE} that {!val:iter_meta} is not implemented using {!val:iter} due to
    the fact this it is performance-cricical. *)

(** [occurs m t] tests whether the metavariable [m] occurs in the term [t]. As
    for {!val:eq}, the behaviour of this function is unspecified when [t] uses
    the [Patt] or [TEnv] constructor. *)
let occurs : meta -> term -> bool = fun m t ->
  let fn p = if m == p then raise Exit in
  try iter_meta fn t; false with Exit -> true

(** [get_metas t] returns the list of all the metavariables in [t]. *)
let get_metas : term -> meta list = fun t ->
  let l = Pervasives.ref [] in
  iter_meta (fun m -> Pervasives.(l := m :: !l)) t;
  List.sort_uniq (fun m1 m2 -> m1.meta_key - m2.meta_key) Pervasives.(!l)

(** [has_metas t] checks that there are metavariables in [t]. *)
let has_metas : term -> bool = fun t ->
  let exception Found in
  try iter_meta (fun _ -> raise Found) t; false with Found -> true

(** [distinct_vars a] checks that [a] is made of distinct variables. *)
let distinct_vars : term array -> bool = fun ar ->
  let rec distinct_vars vars i =
    if i < 0 then true else
    match unfold ar.(i) with
    | Vari(x) when List.exists (Bindlib.eq_vars x) vars -> false
    | Vari(x) -> distinct_vars (x::vars) (i-1)
    | _       -> false
  in
  distinct_vars [] (Array.length ar - 1)

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

(** {3 Subterm position helper module} *)

(** Some tools to encode the position of a subterm in a term. *)
module Subterm =
struct
  (** Each element of the list is a level in the tree of the term.  For
      instance, in the term [Appl(Appl(f, x), Appl(Appl(g, a), b))], the
      subterm [a] has position [1.0], encoded by [[0 ; 1]], [b] has [1.1]
      encoded by [[1 ; 1]] and [x] has [0] encoded by [[0]]. *)
  type t = int list

  (** [compare a b] implements lexicographic order on positions. *)
  let compare : t -> t -> int = fun a b -> Pervasives.compare (List.rev a)
    (List.rev b)

  (** [pp o p] output position [p] to channel [o]. *)
  let pp : t pp = fun oc pos ->
    match pos with
    | [] -> Format.fprintf oc "ε"
    | x  -> List.pp (fun oc -> Format.fprintf oc "%d") "." oc (List.rev x)

  (** Initial position. *)
  let init = []

  (** [succ p] returns the successor of position [p].  For instance, if
      [p = [1 ; 1]], [succ p = [2 ; 1]].  The succ of the initial position is
      the first subterm of this position. *)
  let succ = function
    | []      -> 0 :: init
    | x :: xs -> succ x :: xs

  (** [prefix p q] sets position [p] as prefix of position [q], for instance,
      {i prefix 1 3.4} is {i 1.3.4}; which is represented [prefix [1] [4;3]]
      is [[4;3;1]]. *)
  let prefix : t -> t -> t = fun p q -> q @ p

  (** [sub p] returns the position of the first subterm of [p]. *)
  let sub : t -> t = fun p -> 0 :: p

  (** [tag ?s l] attaches the positions to a list of terms as if they were the
      subterms of a same term.  If [?s] is supplied, the first element of the
      list is at position [s]. *)
  let tag : ?ini:t -> term list -> (term * t) list = fun ?ini xs ->
    let start, p = match ini with
      | None | Some([]) -> 0, init
      | Some(s :: p)    -> s, p in
    List.mapi (fun i e -> (e, prefix p [i + start])) xs
end

(** Functional map with [Subterm.t] as keys *)
module SubtMap = Map.Make(Subterm)
