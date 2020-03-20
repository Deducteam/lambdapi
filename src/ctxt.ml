(** Typing context. *)

open Extra
open Terms

(** [empty] is the empty context. *)
let empty : ctxt = []

(** [unbind ctx a def b] returns the triple [(x,b,ctx')] such that [(x,b)] is
    the unbinding of [b] and [ctx'] is the context [ctx] extended with, if [x]
    occurs in [b]
    - the assumption that [x] is of type [a] if [def] is [None], and
    - the definition of [x] in [def] of type [a] otherwise. *)
let unbind : ctxt -> term -> term option -> tbinder -> tvar * term * ctxt =
  fun ctx a def b ->
  let (x,b') = Bindlib.unbind b in
  let ctx' =
    if Bindlib.binder_occur b then
      match def with
      | None    -> (x, a, None) :: ctx
      | Some(t) -> (x, a, Some(t)) :: ctx
    else ctx
  in
  (x,b',ctx')

(** [find x ctx] returns the type of [x] in the context [ctx] when it appears,
    and raises [Not_found] otherwise. *)
let type_of : tvar -> ctxt -> term = fun x ctx ->
  let (_,a,_) = List.find (fun (y,_,_) -> Bindlib.eq_vars x y) ctx in a

(** [pop_def_of x ctx] returns the definition of [x] in the context [ctx] and
    the context [ctx] without the definition of [x] if [x] appears in [ctx]
    and
    @raise Not_found if [x] does not appear in [ctx]. *)
let pop_def_of : tvar -> ctxt -> term * ctxt = fun x ctx ->
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
let def_of : tvar -> ctxt -> term = fun x ctx ->
  fst (pop_def_of x ctx)

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> ctxt -> bool = fun x ctx ->
  try ignore (type_of x ctx); false with Not_found -> true

(** [to_prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. *)
let to_prod : ctxt -> term -> term = fun ctx t ->
  match ctx with
  | []            -> t
  | [(x,a,None)]  -> Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift t)))
  | _             ->
      let fn t (x,a,_) = _Prod (lift a) (Bindlib.bind_var x t) in
      Bindlib.unbox (List.fold_left fn (lift t) ctx)

(** [make_meta ctx a] creates a metavariable of type [a],  with an environment
    containing the variables of context [ctx]. *)
let make_meta : ctxt -> term -> term = fun ctx a ->
  let m = fresh_meta (to_prod ctx a) (List.length ctx) in
  let getv (x,_,_) = Vari(x) in
  Meta(m, Array.of_list (List.rev_map getv ctx))

(** [sub ctx vs] return the sub-context of [ctx] made of the variables of
    [vs]. *)
let sub : ctxt -> tvar array -> ctxt = fun ctx vs ->
  let f ((x,_,_) as hyp) ctx =
    if Array.exists (Bindlib.eq_vars x) vs then hyp::ctx else ctx
  in
  List.fold_right f ctx []
