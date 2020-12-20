(** Scoping environment for variables. *)

open Lplib

open Terms

(** Type of an environment, used in scoping to associate names to
    corresponding Bindlib variables and types. Note that it cannot be
    implemented by a map as the order is important. The structure is similar
    to then one of {!type:Terms.ctxt}, a tuple [(x,a,t)] is a variable [x],
    its type [a] and possibly its definition [t] *)
type env = (string * (tvar * tbox * tbox option)) list

type t = env

(** [empty] is the empty environment. *)
let empty : env = []

(** [add v a t env] extends the environment [env] by mapping the string
    [Bindlib.name_of v] to [(v,a,t)]. *)
let add : tvar -> tbox -> tbox option -> env -> env = fun v a t env ->
  (Bindlib.name_of v, (v, a, t)) :: env

(** [find n env] returns the Bindlib variable associated to the variable  name
    [n] in the environment [env]. If none is found, [Not_found] is raised. *)
let find : string -> env -> tvar = fun n env ->
  let (x,_,_) = List.assoc n env in x

(** [to_prod env t] builds a sequence of products / let-bindings whose domains
    are the variables of the environment [env] (from left to right), and whose
    body is the term [t]. By calling [to_prod [(xn,an,None);⋯;(x1,a1,None)] t]
    you obtain a term of the form [Πx1:a1,..,Πxn:an,t]. *)
let to_prod_box : env -> tbox -> tbox = fun env t ->
  let fn t (_,(x,a,u)) =
    match u with
    | Some(u) -> _LLet a u (Bindlib.bind_var x t)
    | None    -> _Prod a (Bindlib.bind_var x t)
  in
  List.fold_left fn t env

(** [to_prod] is an “unboxed” version of [to_prod_box]. *)
let to_prod : env -> tbox -> term = fun env t ->
  Bindlib.unbox (to_prod_box env t)

(** [to_abst env t] builds a sequence of abstractions or let bindings,
    depending on the definition of the elements in the environment whose
    domains are the variables of the environment [env] (from left to right),
    and which body is the term [t]:
    [to_abst [(xn,an,None);..;(x1,a1,None)] t = λx1:a1,..,λxn:an,t]. *)
let to_abst : env -> tbox -> term = fun env t ->
  let fn t (_,(x,a,u)) =
    match u with
    | Some(u) -> _LLet a u (Bindlib.bind_var x t)
    | None    -> _Abst a (Bindlib.bind_var x t)
  in
  Bindlib.unbox (List.fold_left fn t env)

(** [vars env] extracts the array of the {e not defined} Bindlib variables in
    [env]. Note that the order is reversed: [vars [(xn,an);..;(x1,a1)] =
    [|x1;..;xn|]]. *)
let vars : env -> tvar array = fun env ->
  let f (_, (x, _, u)) = if u = None then Some(x) else None in
  Array.of_list (List.filter_rev_map f env)

(** [to_tbox env] extracts the array of the {e not defined} variables in [env]
    and injects them in the [tbox] type.  This is the same as [Array.map _Vari
    (vars env)]. Note that the order is reversed: [vars [(xn,an);..;(x1,a1)] =
    [|x1;..;xn|]]. *)
let to_tbox : env -> tbox array = fun env ->
  let f (_, (x, _, u)) = if u = None then Some(_Vari x) else None in
  Array.of_list (List.filter_rev_map f env)

(** [to_ctxt env] builds a context made from undefined variables of
    environment [env]. *)
let to_ctxt : env -> ctxt =
  let f (_,(v,bt,bu)) = (v, Bindlib.unbox bt, Option.map Bindlib.unbox bu) in
  List.map f

(** [destruct_prod n t] returns a tuple [(env,b)] where [b] is constructed
   from the term [t] by unbinding [n] dependent products. The free variables
   created by this process are given (with their types) in the environment
   [env] (in reverse order). For instance, if [t] is of the form [Πx1:a1, ⋯,
   Πxn:an, b] then the function returns [b] and the environment [(xn,an);
   ⋯;(x1,a1)]. [n] must be non-negative.
@raise [Invalid_argument] if [t] does not evaluate to a series of (at least)
   [n] products. *)
let destruct_prod : int -> term -> env * term = fun n t ->
  let rec build_env i env t =
    if i >= n then (env, t) else
    match Eval.whnf [] t with
    | Prod(a,b) ->
        let (x, b) = Bindlib.unbind b in
        build_env (i+1) (add x (lift (Eval.simplify [] a)) None env) b
    | _         -> invalid_arg (__LOC__ ^ "destruct_prod")
  in
  build_env 0 [] t

(** [env_of_prod xs t] is similar to [destruct_prod n t] where [n =
   Array.length xs] except that it does not return the final codomain [b] and
   replaces unbound variables by those of [xs].
@raise [Invalid_argument] if [t] does not evaluate to a series of (at least)
   [n] products. *)
let env_of_prod : tvar array -> term -> env = fun xs t ->
  let n = Array.length xs in
  let rec build_env i env t =
    if i >= n then env else
    match Eval.whnf [] t with
    | Prod(a,b) -> let env = add xs.(i) (lift a) None env in
                   build_env (i+1) env (Bindlib.subst b (Vari(xs.(i))))
    | _         -> invalid_arg (__LOC__ ^ "env_of_prod")
  in
  build_env 0 [] t
