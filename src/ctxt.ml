(** Typing context. *)

open Extra
open Terms

type t = ctxt

(** [empty] is the empty context. *)
let empty : t = []

(** [assume h ctx] adds list of assumptions [h] mapping variables to their
    types to context [ctx]. *)
let assume : (tvar * term) list -> t -> t = fun hyps ctx ->
  List.map (fun (x,a) -> (x, a, None)) hyps @ ctx

(** [define x a t ctx] maps variable [x] to term [t] of type [a] in [ctx]. *)
let define : tvar -> term -> term -> t -> t = fun x a t ctx ->
  (x, a, Some(t)) :: ctx

(** [unbind_ctxt ctx a ?def b] returns the triple [(x,b,ctx')] such that
    [(x,b)] is the unbinding of [b] and [ctx'] is the context [ctx] extended
    with, if [x] occurs in [b]
    - [Assume(x, a)] if [?def] is not given and
    - [Define{ctx_v=x; ctx_y=a; ctx_e=?def}] otherwise. *)
let unbind : t -> term -> ?def:term -> tbinder -> tvar * term * t =
  fun ctx a ?def b ->
  let (x,b') = Bindlib.unbind b in
  let ctx' =
    if Bindlib.binder_occur b then
      match def with
      | None    -> assume [(x,a)] ctx
      | Some(t) -> define x a t ctx
    else ctx
  in
  (x,b',ctx')

(** [assumptions ctx] returns a list mapping free variable to their types. *)
let assumptions : t -> (tvar * term) list =
  List.map (fun (x,a,_) -> (x, a))

(** [find x ctx] returns the type of [x] in the context [ctx] when it appears,
    and raises [Not_found] otherwise. *)
let type_of : tvar -> t -> term = fun x ctx ->
  let (_,a,_) = List.find (fun (y,_,_) -> Bindlib.eq_vars x y) ctx in a

(** [pop_def_of x ctx] returns the definition of [x] in the context [ctx] and
    the context [ctx] without the definition of [x] if [x] appears in [ctx]
    and
    @raise Not_found if [x] does not appear in [ctx]. *)
let pop_def_of : tvar -> t -> term * t = fun x ctx ->
  let rec pop_def_of dec inc =
  match dec with
    | (y,_,Some(t))::l when Bindlib.eq_vars x y -> (t, List.rev_append inc l)
    | h::l                                      -> pop_def_of l (h::inc)
    | []                                        -> raise Not_found
  in
  pop_def_of ctx []

(** [def_of x ctx] returns the definition of [x] in the context [ctx] if it
    appears, and
    @raise Not_found if not. *)
let def_of : tvar -> t -> term = fun x ctx ->
  fst (pop_def_of x ctx)

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> t -> bool = fun x ctx ->
  try ignore (type_of x ctx); false with Not_found -> true

(** [to_prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. *)
let to_prod : t -> term -> term = fun ctx t ->
  match ctx with
  | []            -> t
  | [(x,a,None)]  -> Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift t)))
  | _             ->
      let fn t (x,a,_) = _Prod (lift a) (Bindlib.bind_var x t) in
      Bindlib.unbox (List.fold_left fn (lift t) ctx)

(** [make_meta ctx a] creates a metavariable of type [a],  with an environment
    containing the variables of context [ctx]. *)
let make_meta : t -> term -> term = fun ctx a ->
  let m = fresh_meta (to_prod ctx a) (List.length ctx) in
  let getv (x,_,_) = Vari(x) in
  Meta(m, Array.of_list (List.rev_map getv ctx))

(** [sub ctx vs] return the sub-context of [ctx] made of the variables of
    [vs]. *)
let sub : t -> tvar array -> t = fun ctx vs ->
  let f ((x,_,_) as hyp) ctx =
    if Array.exists (Bindlib.eq_vars x) vs then hyp::ctx else ctx
  in
  List.fold_right f ctx []
