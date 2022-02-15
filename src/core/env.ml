(** Scoping environment for variables. *)

open Lplib
open Term

(** Type of an environment, used in scoping to associate names to
    corresponding variables and types. Note that it cannot be
    implemented by a map as the order is important. The structure is similar
    to then one of {!type:Term.ctxt}, a tuple [(x,a,t)] is a variable [x],
    its type [a] and possibly its definition [t] *)
type env = (string * (tvar * term * term option)) list

type t = env

(** [empty] is the empty environment. *)
let empty : env = []

(** [add v a t env] extends the environment [env] by mapping the string
    [n] to [(v,a,t)]. *)
let add : string -> tvar -> term -> term option -> env -> env =
  fun n v a t env -> (n, (v, a, t)) :: env

(** [find n env] returns the variable associated to the variable  name
    [n] in the environment [env]. If none is found, [Not_found] is raised. *)
let find : string -> env -> tvar = fun n env ->
  let (x,_,_) = List.assoc n env in x

(** [mem n env] returns [true] iff [n] is mapped to a variable in [env]. *)
let mem : string -> env -> bool = List.mem_assoc

(** [to_prod env t] builds a sequence of products / let-bindings whose domains
    are the variables of the environment [env] (from left to right), and whose
    body is the term [t]. By calling [to_prod [(xn,an,None);⋯;(x1,a1,None)] t]
    you obtain a term of the form [Πx1:a1,..,Πxn:an,t]. *)
let to_prod : env -> term -> term = fun env t ->
  let add_prod t (_,(x,a,u)) =
    let b = bind_var x t in
    match u with
    | Some u -> mk_LLet (a, u, b)
    | None -> mk_Prod (a, b)
  in
  List.fold_left add_prod t env

(** [to_abst env t] builds a sequence of abstractions or let bindings,
    depending on the definition of the elements in the environment whose
    domains are the variables of the environment [env] (from left to right),
    and which body is the term [t]:
    [to_abst [(xn,an,None);..;(x1,a1,None)] t = λx1:a1,..,λxn:an,t]. *)
let to_abst : env -> term -> term = fun env t ->
  let add_abst t (_,(x,a,u)) =
    let b = bind_var x t in
    match u with
    | Some u -> mk_LLet (a, u, b)
    | None -> mk_Abst (a, b)
  in
  List.fold_left add_abst t env

(** [vars env] extracts the array of the {e not defined} variables in
    [env]. Note that the order is reversed: [vars [(xn,an);..;(x1,a1)] =
    [|x1;..;xn|]]. *)
let vars : env -> tvar array = fun env ->
  let f (_, (x, _, u)) = if u = None then Some(x) else None in
  Array.of_list (List.filter_rev_map f env)

(** [appl t env] applies [t] to the variables of [env]. *)
let appl : term -> env -> term = fun t env ->
  List.fold_right (fun (_,(x,_,_)) t -> mk_Appl (t, mk_Vari x)) env t

(** [to_terms env] extracts the array of the {e not defined} variables in
   [env] and injects them in the [tbox] type.  This is the same as [Array.map
   _Vari (vars env)]. Note that the order is reversed: [to_terms
   [(xn,an);..;(x1,a1)] = [|x1;..;xn|]]. *)
let to_terms : env -> term array = fun env ->
  let f (_, (x, _, u)) = if u = None then Some(mk_Vari x) else None in
  Array.of_list (List.filter_rev_map f env)

(** [to_ctxt e] converts an environment into a context. *)
let to_ctxt : env -> ctxt = List.map snd

(** [match_prod c t f] returns [f a b] if [t] matches [Prod(a,b)] possibly
   after reduction.
@raise [Invalid_argument] if [t] is not a product. *)
let match_prod : ctxt -> term -> (term -> tbinder -> 'a) -> 'a = fun c t f ->
  match unfold t with
  | Prod(a,b) -> f a b
  | _ ->
      match Eval.whnf c t with
      | Prod(a,b) -> f a b
      | _ -> invalid_arg __LOC__

(** [of_prod c s t] returns a tuple [(env,b)] where [b] is constructed from
   the term [t] by unbinding as much dependent products as possible in the
   head of [t]. The free variables created by this process, prefixed by [s],
   are given (with their types) in the environment [env] (in reverse
   order). For instance, if [t] is of the form [Πx1:a1, ⋯, Πxn:an, b], then
   the function returns [b] and the environment [(xn,an); ⋯;(x1,a1)]. *)
let of_prod : ctxt -> string -> term -> env * term = fun c s t ->
  let i = Stdlib.ref (-1) in
  let rec build_env env t =
    try match_prod c t (fun a b ->
            let name = Stdlib.(incr i; s ^ string_of_int !i) in
            let x, b = LibTerm.unbind_name name b in
            build_env (add name x a None env) b)
    with Invalid_argument _ -> env, t
  in build_env [] t

(** [of_prod_nth c n t] returns a tuple [(env,b)] where [b] is constructed
   from the term [t] by unbinding [n] dependent products. The free variables
   created by this process are given (with their types) in the environment
   [env] (in reverse order). For instance, if [t] is of the form [Πx1:a1, ⋯,
   Πxn:an, b] then the function returns [b] and the environment [(xn,an);
   ⋯;(x1,a1)]. [n] must be non-negative.
@raise [Invalid_argument] if [t] does not evaluate to a series of (at least)
   [n] products. *)
let of_prod_nth : ctxt -> int -> term -> env * term = fun c n t ->
  let rec build_env i env t =
    if i >= n then env, t
    else match_prod c t (fun a b ->
             let x, b = unbind b in
             build_env (i+1) (add (name_of x) x a None env) b)
  in build_env 0 [] t

(** [of_prod_using c xs t] is similar to [of_prod s c n t] where [n =
   Array.length xs] except that it replaces unbound variables by those of
   [xs].
@raise [Invalid_argument] if [t] does not evaluate to a series of (at least)
   [n] products. *)
let of_prod_using : ctxt -> tvar array -> term -> env * term = fun c xs t ->
  let n = Array.length xs in
  let rec build_env i env t =
    if i >= n then env, t
    else match_prod c t (fun a b ->
             let xi = xs.(i) in
             let name = name_of xi in
             let env = add name xi a None env in
             build_env (i+1) env (subst b (mk_Vari xi)))
  in build_env 0 [] t
