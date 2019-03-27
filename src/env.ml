(** Scoping environment for variables. *)

open Terms

(** Type of an environment,  used in scoping to associate names
    to corresponding Bindlib variables and types. *)
type env = (string * (tvar * tbox)) list

type t = env

(** [empty] is the empty environemnt. *)
let empty : env = []

(** [add n x a env] extends the environment [env] by mapping the variable name
    [n] to [(x,a)] (only when [s] is not the wildcard symbol ["_"]). *)
let add : string -> tvar -> tbox -> env -> env = fun n x a env ->
  if n = "_" then env else (n,(x,a))::env

(** [find n env] returns the Bindlib variable associated to the variable  name
    [n] in the environment [env]. If none is found, [Not_found] is raised. *)
let find : string -> env -> tvar = fun n env ->
  fst (List.assoc n env)

(** [to_prod env t] builds a sequence of products whose  domains  are the
    variables of the environment [env] (from left to right), and which body is
    the term [t]: [to_prod [(xn,an);..;(x1,a1)] t = ∀x1:a1,..,xn:an,t]. *)
let to_prod : env -> tbox -> term = fun env t ->
  let fn t (_,(x,a)) = _Prod a (Bindlib.bind_var x t) in
  Bindlib.unbox (List.fold_left fn t env)

(** [vars env] extracts the array of the Bindlib variables in [env] and
   injects them into the [tbox] type. Note that the order is reversed:
   [vars [(xn,an);..;(x1,a1)] = [|x1;..;xn|]. *)
let vars : env -> tbox array = fun env ->
  Array.of_list (List.rev_map (fun (_,(x,_)) -> _Vari x) env)

(** [of_prod xs t] returns the environment [(xn,an),..,(x1,a1)] if [t] is of
   the form [∀x1:a1,..,∀xn:an,b]. Raises [Invalid_argument] if [t] is not of
   this form. *)
let of_prod : tvar array -> term -> env = fun vars t ->
  let n = Array.length vars in
  let rec build_env i env t =
    if i >= n then env
    else match unfold t with
         | Prod(a,b) ->
            let v = vars.(i) in
            let env = (Bindlib.name_of v, (v,lift a))::env in
            build_env (i+1) env (Bindlib.subst b (Vari v))
         | _ -> raise (Invalid_argument "of_prod")
  in build_env 0 [] t
