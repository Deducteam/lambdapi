(** Typing context. *)

open Extra
open Terms

(** [unbind ctx a def b] returns a triple [(x,t,new_ctx)] such that [(x,t)] is
    an unbinding of [b] (in the sense of [Bindlib.unbind]) and [new_ctx] is an
    extension of context [ctx] with the assumption that [x] has type [a] (only
    if [x] occurs in [t]). If [def] is of the form [Some(u)], the context also
    registers the term [u] as the definition of variable [x]. *)
let unbind : ctxt -> term -> term option -> tbinder ->
  tvar * term * ctxt = fun ctx a def b ->
  let (x, t) = Bindlib.unbind b in
  (x, t, if Bindlib.binder_occur b then (x, a, def) :: ctx else ctx)

(** [type_of x ctx] returns the type of [x] in the context [ctx] when it
    appears, and raises [Not_found] otherwise. *)
let type_of : tvar -> ctxt -> term = fun x ctx ->
  let (_,a,_) = List.find (fun (y,_,_) -> Bindlib.eq_vars x y) ctx in a

(** [def_of x ctx] returns the definition of [x] in the context [ctx] if it
    appears, and [None] otherwise *)
let rec def_of : tvar -> ctxt -> term option = fun x ctx ->
  match ctx with
  | []         -> None
  | (y,_,d)::l -> if Bindlib.eq_vars x y then d else def_of x l

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> ctxt -> bool = fun x ->
  List.exists (fun (y,_,_) -> Bindlib.eq_vars x y)

(** [prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. It returns the number of products as well. *)
let prod : ctxt -> term -> term * int = fun ctx t ->
  let fn (t,c) elt =
    match elt with
    | (x,a,None   ) -> (_Prod (lift a) (Bindlib.bind_var x t), c + 1)
    | (x,a,Some(u)) -> (_LLet (lift u) (lift a) (Bindlib.bind_var x t), c)
  in
  let t, c = List.fold_left fn (lift t, 0) ctx in
  (Bindlib.unbox t, c)

(** [sub ctx vs] returns the sub-context of [ctx] made of the variables of
    [vs]. *)
let sub : ctxt -> tvar array -> ctxt = fun ctx vs ->
  let f ((x,_,_) as hyp) ctx =
    if Array.exists (Bindlib.eq_vars x) vs then hyp::ctx else ctx
  in
  List.fold_right f ctx []

(** [merge c1 c2] merges contexts [c1] and [c2] and returns [None] if they
    overlap. The new context is [c1] reversed and concatenated to [c2]. *)
let rec merge : ctxt -> ctxt -> ctxt option = fun c1 c2 ->
  match c1 with
  | (x,_,_)::_ when mem x c2 -> None
  | (x,a,d)::c1 -> merge c1 ((x,a,d)::c2)
  | []          -> Some(c2)
