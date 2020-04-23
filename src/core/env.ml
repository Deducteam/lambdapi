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

(** [destruct_prod n prod] returns a tuple [(env, a)] where [a] is constructed
    from the term [prod] by destructing (i.e., by unbinding with the [Bindlib]
    terminology) a total [n] dependent products. The free variables created by
    the process are are given (with their types) in the environment [env]. The
    function raises [Invalid_argument] if [prod] does not evaluate to a series
    of (at least) [n] product types. Intuitively, if the term [prod] is of the
    form [Π (x1:a1) ⋯ (xn:an), a] then the function (roughly) returns [a], and
    the environment [(xn, an) ; ⋯ ; (x1, a1)]. *)
let destruct_prod : int -> term -> env * term = fun n t ->
  let rec build_env i env t =
    if i >= n then (env, t) else
    match Eval.whnf [] t with
    | Prod(a,b) ->
        let (x, b) = Bindlib.unbind b in
        build_env (i+1) (add x (lift (Eval.simplify [] a)) None env) b
    | _         -> invalid_arg "destruct_prod"
  in
  build_env 0 [] t

(** [copy_prod_env xs prod] constructs an environment mapping the variables of
    [xs] to successive dependent product type domains of the term [prod]. Note
    that dependencies are preserved in the process,  and types of the produced
    environment can hence refer to other variables of the environment whenever
    this is necessary. Note that the produced environment is equivalent to the
    environment [fst (destruct_prod (Array,length xs) prod)] if the variables
    of its domain are substituted by those of [xs]. Intuitively,  if [prod] is
    of the form [Π (y1:a1) ⋯ (yn:an), a]  then the environment returned by the
    function is (roughly) [(xn, an{y1≔x1, ⋯, yn-1≔xn-1}) ; ⋯ ; (x1, a1)]. Note
    that the function raises [Invalid_argument] if [prod] does not evaluate to
    a sequence of [Array.length xs] dependent products. *)
let copy_prod_env : tvar array -> term -> env = fun xs t ->
  let n = Array.length xs in
  let rec build_env i env t =
    if i >= n then env else
    match Eval.whnf [] t with
    | Prod(a,b) -> let env = add xs.(i) (lift a) None env in
                   build_env (i+1) env (Bindlib.subst b (Vari(xs.(i))))
    | _         -> invalid_arg "of_prod_vars"
  in
  build_env 0 [] t

(** Given a metavariable [m] of arity [n] and type [Πx1:A1,..,Πxn:An,B] (with
   [B] being a sort normally), [extend_meta_type m] returns
   [m[x1,..,xn],(Πy:p,q),bp,bq] where p=m1[x1,..,xn], q=m2[x1,..,xn,y], bp is
   a mbinder of [x1,..,xn] over p, and bq is a mbinder of [x1,..,xn] over q,
   where [y] is a fresh variable, and [m1] and [m2] are fresh metavariables of
   arity [n] and [n+1], and type [Πx1:A1,..,Πxn:An,TYPE] and
   [Πx1:A1,..,Πxn:An,Πy:m1[x1,..,xn],B] respectively. *)
let extend_meta_type : meta -> term * term *
    tmbinder * (term, tbinder) Bindlib.mbinder = fun m ->
  let n = m.meta_arity in
  let (env, s) = destruct_prod n Timed.(!(m.meta_type)) in
  let vs = vars env in
  let xs = Array.map _Vari vs in

  let t1 = to_prod env _Type in
  let m1 = fresh_meta t1 n in

  let y = Bindlib.new_var mkfree "y" in
  let env = add y (_Meta m1 xs) None env in
  let t2 = to_prod env (lift s) in
  let m2 = fresh_meta t2 (n+1) in

  let r1 = Bindlib.unbox (_Meta m xs) in
  let p = _Meta m1 xs in
  let q = Bindlib.bind_var y (_Meta m2 (Array.append xs [|_Vari y|])) in
  let r2 = Bindlib.unbox (_Prod p q) in

  let f x = Bindlib.unbox (Bindlib.bind_mvar vs x) in
  r1, r2, f p, f q

(** [to_ctxt env] builds a context made from undefined variables of
    environment [env]. *)
let to_ctxt : env -> ctxt =
  let f (_,(v,bt,bu)) = (v, Bindlib.unbox bt, Option.map Bindlib.unbox bu) in
  List.map f
