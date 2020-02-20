(** Scoping environment for variables. *)

open Terms

(** Type of an environment, used in scoping to associate names to
   corresponding Bindlib variables and types. Note that it cannot be
   implemented by a map as the order is important. *)
type env = (string * (tvar * tbox)) list

type t = env

(** [empty] is the empty environemnt. *)
let empty : env = []

(** [add v a env] extends the environment [env] by mapping the string
   [Bindlib.name_of v] to [(v,a)]. *)
let add : tvar -> tbox -> env -> env = fun v a env ->
  (Bindlib.name_of v, (v, a)) :: env

(** [find n env] returns the Bindlib variable associated to the variable  name
    [n] in the environment [env]. If none is found, [Not_found] is raised. *)
let find : string -> env -> tvar = fun n env ->
  fst (List.assoc n env)

(** [to_prod env t] builds a sequence of products whose  domains  are the
    variables of the environment [env] (from left to right), and which body is
    the term [t]: [to_prod [(xn,an);..;(x1,a1)] t = ∀x1:a1,..,∀xn:an,t]. *)
let to_prod : env -> tbox -> term = fun env t ->
  let fn t (_,(x,a)) = _Prod a (Bindlib.bind_var x t) in
  Bindlib.unbox (List.fold_left fn t env)

(** [to_abst env t] builds a sequence of abstractions whose  domains  are the
    variables of the environment [env] (from left to right), and which body is
    the term [t]: [to_prod [(xn,an);..;(x1,a1)] t = λx1:a1,..,λxn:an,t]. *)
let to_abst : env -> tbox -> term = fun env t ->
  let fn t (_,(x,a)) = _Abst a (Bindlib.bind_var x t) in
  Bindlib.unbox (List.fold_left fn t env)

(** [vars env] extracts the array of the Bindlib variables in [env]. Note that
    the order is reversed: [vars [(xn,an);..;(x1,a1)] = [|x1;..;xn|]]. *)
let vars : env -> tvar array = fun env ->
  Array.of_list (List.rev_map (fun (_,(x,_)) -> x) env)

(** [to_term env] extracts the array of the variables in [env] and inject them
    in the [tbox] type. This is the same as [Array.map _Vari (vars env)]. Note
    that the order is reversed: [vars [(xn,an);..;(x1,a1)] = [|x1;..;xn|]]. *)
let to_tbox : env -> tbox array = fun env ->
  Array.of_list (List.rev_map (fun (_,(x,_)) -> _Vari x) env)

(** [of_prod n t] returns the environment [(xn,an),..,(x1,a1)] and the term
   [b] if [t] is of the form [∀x1:a1,..,∀xn:an,b]. Raises [Invalid_argument]
   if [t] is not of this form. *)
let of_prod_arity : int -> term -> env * term = fun n t ->
  let rec build_env i env t =
    if i >= n then env, t
    else match Eval.whnf t with
         | Prod(a,b) ->
            let v,b = Bindlib.unbind b in
            let a = Eval.simplify a in
            let env = add v (lift a) env in
            build_env (i+1) env b
         | _ -> raise (Invalid_argument "of_prod")
  in build_env 0 [] t

(** [of_prod vs t] returns the environment [(vn,an{x1=v1,..,xn-1=vn-1}),..,
   (v1,a1)] and the term [b{x1=v1,..,xn=vn}] if [t] is of the form
   [∀x1:a1,..,∀xn:an,b]. Raises [Invalid_argument] if [t] is not of this
   form. *)
let of_prod_vars : tvar array -> term -> env * term = fun vars t ->
  let n = Array.length vars in
  let rec build_env i env t =
    if i >= n then env, t
    else match Eval.whnf t with
         | Prod(a,b) ->
            let v = vars.(i) in
            let env = add v (lift a) env in
            build_env (i+1) env (Bindlib.subst b (Vari v))
         | _ -> raise (Invalid_argument "of_prod")
  in build_env 0 [] t

(** [to_ctxt] builds a context from an environment. *)
let to_ctxt : t -> ctxt =
  List.map (fun (_,(v,bt)) -> Assume(v,Bindlib.unbox bt))
