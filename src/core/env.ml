(** Scoping environment for variables.
    Note that since meta-variable types are closed, the contexts passed to
    {!val:Eval.whnf} and alike are empty. *)

open Extra
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

(** [to_prod env t] builds a sequence of products or let-bindings whose
    domains are the variables of the environment [env] (from left to right),
    and which body is the term [t]:
    [to_prod [(xn,an,None);..;(x1,a1,None)] t = ∀x1:a1,..,∀xn:an,t]. *)
let to_prod : env -> tbox -> term = fun env t ->
  let fn t (_,(x,a,u)) =
    match u with
    | Some(u) -> _LLet u a (Bindlib.bind_var x t)
    | None    -> _Prod a (Bindlib.bind_var x t)
  in
  Bindlib.unbox (List.fold_left fn t env)

(** [to_abst env t] builds a sequence of abstractions or let bindings,
    depending on the definition of the elements in the environment whose
    domains are the variables of the environment [env] (from left to right),
    and which body is the term [t]:
    [to_abst [(xn,an,None);..;(x1,a1,None)] t = λx1:a1,..,λxn:an,t]. *)
let to_abst : env -> tbox -> term = fun env t ->
  let fn t (_,(x,a,u)) =
    match u with
    | Some(u) -> _LLet u a (Bindlib.bind_var x t)
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

(** [of_prod_arity n t] returns the environment [(xn,an),..,(x1,a1)] and the
    term [b] if [t] is of the form [∀x1:a1,..,∀xn:an,b].
    @raise Invalid_argument if [t] is not of this form. *)
let of_prod_arity : int -> term -> env * term = fun n t ->
  let rec build_env i env t =
    if i >= n then (env, t) else
    match Eval.whnf [] t with
      | Prod(a,b) ->
          let v,b = Bindlib.unbind b in
          let a = Eval.simplify [] a in
          let env = add v (lift a) None env in
          build_env (i+1) env b
      | _         -> raise (Invalid_argument "of_prod_arity")
  in
  build_env 0 [] t

(** [of_prod vs t] returns the environment [(vn,an{x1=v1,..,xn-1=vn-1}),..,
    (v1,a1)] and the term [b{x1=v1,..,xn=vn}] if [t] is of the form
    [∀x1:a1,..,∀xn:an,b]. Raises [Invalid_argument] if [t] is not of this
    form. *)
let of_prod_vars : tvar array -> term -> env * term = fun vars t ->
  let n = Array.length vars in
  let rec build_env i env t =
    if i >= n then (env, t) else
    match Eval.whnf [] t with
      | Prod(a,b) ->
          let v = vars.(i) in
          let env = add v (lift a) None env in
          build_env (i+1) env (Bindlib.subst b (Vari v))
      | _         -> raise (Invalid_argument "of_prod_vars")
  in
  build_env 0 [] t

(** [to_ctxt env] builds a context made from undefined variables of
    environment [env]. *)
let to_ctxt : env -> ctxt =
  let f (_,(v,bt,bu)) = (v, Bindlib.unbox bt, Option.map Bindlib.unbox bu) in
  List.map f
