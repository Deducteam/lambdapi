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

(** [llet ctx t] builds one let-binding on top of [t] for each defined
    variable in [ctx]. *)
let rec llet ctx t =
  match ctx with
  | []                 -> t
  | (_,_,None)::ctx    -> llet ctx t
  | (x,a,Some(u))::ctx ->
      let body = Bindlib.bind_var x (lift t) in
      llet ctx (LLet(u,a,Bindlib.unbox body))

(** [sub ctx vs] returns the sub-context of [ctx] made of the variables of
    [vs]. *)
let sub : ctxt -> tvar array -> ctxt = fun ctx vs ->
  let f ((x,_,_) as hyp) ctx =
    if Array.exists (Bindlib.eq_vars x) vs then hyp::ctx else ctx
  in
  List.fold_right f ctx []
