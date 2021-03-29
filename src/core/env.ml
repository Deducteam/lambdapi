(** Scoping environment for variables. *)

open Lplib
open Term

(** Type of an environment, used in scoping to associate names to
    corresponding Bindlib variables and types. Note that it cannot be
    implemented by a map as the order is important. The structure is similar
    to then one of {!type:Term.ctxt}, a tuple [(x,a,t)] is a variable [x],
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
  let add_prod t (_,(x,a,u)) =
    match u with
    | Some(u) -> _LLet a u (Bindlib.bind_var x t)
    | None    -> _Prod a (Bindlib.bind_var x t)
  in
  List.fold_left add_prod t env

(** [to_prod] is an “unboxed” version of [to_prod_box]. *)
let to_prod : env -> tbox -> term = fun env t ->
  Bindlib.unbox (to_prod_box env t)

(** [to_abst env t] builds a sequence of abstractions or let bindings,
    depending on the definition of the elements in the environment whose
    domains are the variables of the environment [env] (from left to right),
    and which body is the term [t]:
    [to_abst [(xn,an,None);..;(x1,a1,None)] t = λx1:a1,..,λxn:an,t]. *)
let to_abst : env -> tbox -> term = fun env t ->
  let add_abst t (_,(x,a,u)) =
    match u with
    | Some(u) -> _LLet a u (Bindlib.bind_var x t)
    | None    -> _Abst a (Bindlib.bind_var x t)
  in
  Bindlib.unbox (List.fold_left add_abst t env)

(** [vars env] extracts the array of the {e not defined} Bindlib variables in
    [env]. Note that the order is reversed: [vars [(xn,an);..;(x1,a1)] =
    [|x1;..;xn|]]. *)
let vars : env -> tvar array = fun env ->
  let f (_, (x, _, u)) = if u = None then Some(x) else None in
  Array.of_list (List.filter_rev_map f env)

(** [to_tbox env] extracts the array of the {e not defined} variables in [env]
   and injects them in the [tbox] type.  This is the same as [Array.map _Vari
   (vars env)]. Note that the order is reversed: [to_tbox [(xn,an);..;(x1,a1)]
   = [|x1;..;xn|]]. *)
let to_tbox : env -> tbox array = fun env ->
  let f (_, (x, _, u)) = if u = None then Some(_Vari x) else None in
  Array.of_list (List.filter_rev_map f env)

(** [to_ctxt e] converts an environment into a context. *)
let to_ctxt : env -> ctxt =
  List.map
    (fun (_,(v,a,t)) -> (v, Bindlib.unbox a, Option.map Bindlib.unbox t))

(** [match_prod c t f] returns [f a b] if [t] matches [Prod(a,b)] possibly
   after reduction. *)
let match_prod : ctxt -> term -> (term -> tbinder -> 'a) -> 'a = fun c t f ->
  match unfold t with
  | Prod(a,b) -> f a b
  | _ ->
      match Eval.whnf c t with
      | Prod(a,b) -> f a b
      | _ -> invalid_arg __LOC__

(** [of_prod c n t] returns a tuple [(env,b)] where [b] is constructed
   from the term [t] by unbinding [n] dependent products. The free variables
   created by this process are given (with their types) in the environment
   [env] (in reverse order). For instance, if [t] is of the form [Πx1:a1, ⋯,
   Πxn:an, b] then the function returns [b] and the environment [(xn,an);
   ⋯;(x1,a1)]. [n] must be non-negative.
@raise [Invalid_argument] if [t] does not evaluate to a series of (at least)
   [n] products. *)
let of_prod : ctxt -> int -> term -> env * term = fun c n t ->
  let rec build_env i env t =
    if i >= n then (env, t)
    else match_prod c t (fun a b ->
             let (x, b) = Bindlib.unbind b in
             build_env (i+1) (add x (lift a) None env) b)
  in build_env 0 [] t

(** [of_prod_using c xs t] is similar to [of_prod c n t] where [n =
   Array.length xs] except that it replaces unbound variables by those of
   [xs].
@raise [Invalid_argument] if [t] does not evaluate to a series of (at least)
   [n] products. *)
let of_prod_using : ctxt -> tvar array -> term -> env * term = fun c xs t ->
  let n = Array.length xs in
  let rec build_env i env t =
    if i >= n then env, t
    else match_prod c t (fun a b ->
             let env = add xs.(i) (lift a) None env in
             build_env (i+1) env (Bindlib.subst b (Vari(xs.(i)))))
  in build_env 0 [] t

(** [fresh_meta_Type env] creates a fresh metavariable of type [Type] in
    environment [env]. *)
let fresh_meta_Type : t -> tbox = fun env ->
  let vs = to_tbox env in
  let arity = Array.length vs in
  let tm = to_prod_box env _Type in
  _Meta_full (Meta.fresh_box tm arity) vs

(** [fresh_meta_tbox env] creates a _Meta tbox from a fresh metavariable whose
   type is itself a fresh metavariable of type [fresh_meta_Type env]. *)
let fresh_meta_tbox : env -> tbox = fun env ->
  let vs = to_tbox env in
  let arity = Array.length vs in
  let tm =
    let x = Meta.fresh_box (to_prod_box env _Type) arity in
    to_prod_box env (_Meta_full x vs)
  in
  _Meta_full (Meta.fresh_box tm arity) vs

(** [fresh_meta env] creates a Meta term from a fresh metavariable whose type
   is a fresh metavariable of type [to_prod env Type]. *)
let fresh_meta : env -> term = fun env -> Bindlib.unbox (fresh_meta_tbox env)

(** [add_fresh_metas env t n] returns the application of [t] to [n] fresh meta
   terms. *)
let add_fresh_metas : env -> term -> int -> term = fun env ->
  let rec add t n = if n <= 0 then t else add (Appl(t, fresh_meta env)) (n-1)
  in add
