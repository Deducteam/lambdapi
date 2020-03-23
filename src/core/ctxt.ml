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
  let ctx' = if Bindlib.binder_occur b then (x, a, def) :: ctx else ctx in
  (x,b',ctx')

(** [find x ctx] returns the type of [x] in the context [ctx] when it appears,
    and raises [Not_found] otherwise. *)
let type_of : tvar -> ctxt -> term = fun x ctx ->
  let (_,a,_) = List.find (fun (y,_,_) -> Bindlib.eq_vars x y) ctx in a

(** [def_of x ctx] returns the definition of [x] in the context [ctx] if it
    appears, and [None] otherwise *)
let rec def_of : tvar -> ctxt -> term option = fun x ctx ->
  match ctx with
  | []         -> None
  | (y,_,d)::l ->
      if Bindlib.eq_vars x y then d else
      def_of x l

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> ctxt -> bool = fun x ->
  List.exists (fun (y,_,_) -> Bindlib.eq_vars x y)

(** [to_prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. *)
let to_prod : ctxt -> term -> term = fun ctx t ->
  let fn t elt =
    match elt with
    | (x,a,None   ) -> _Prod (lift a) (Bindlib.bind_var x t)
    | (x,a,Some(u)) -> _LLet (lift u) (lift a) (Bindlib.bind_var x t)
  in
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
