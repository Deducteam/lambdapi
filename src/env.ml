(** Environment for variables. *)

open Terms

(** Type of an environment,  used to associate variable names to corresponding
    Bindlib variables and types. *)
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

(** [prod_of_env env t] builds a sequence of product types whose  domains  are
    variables of the environment [env] (from left to right), and which body is
    the term [t]. *)
let prod_of_env : env -> tbox -> term = fun env t ->
  let fn t (_,(x,a)) = _Prod a (Bindlib.bind_var x t) in
  Bindlib.unbox (List.fold_left fn t env)

(** [vars_of_env env] extracts the array of the Bindlib variables in [env] and
    injects them into the [tbox] type. Note that the order is reversed. *)
let vars_of_env : env -> tbox array = fun env ->
  Array.of_list (List.rev_map (fun (_,(x,_)) -> _Vari x) env)
