(** Typing context. *)

open Term
open Timed

(** [unbind ctx a def b] returns a triple [(x,t,new_ctx)] such that [(x,t)] is
   an unbinding of [b] (in the sense of [Bindlib.unbind]) and [new_ctx] is an
   extension of the context [ctx] with the declaration that [x] has type [a]
   (only if [x] occurs in [t]). If [def] is of the form [Some(u)], the context
   also registers the term [u] as the definition of variable [x]. *)
let unbind : ctxt -> term -> term option -> tbinder -> tvar * term * ctxt =
  fun ctx a def b ->
  let (x, t) = Bindlib.unbind b in
  (x, t, if Bindlib.binder_occur b then (x, a, def) :: ctx else ctx)

(** [type_of x ctx] returns the type of [x] in the context [ctx] when it
    appears in it, and
@raise [Not_found] otherwise. *)
let type_of : tvar -> ctxt -> term = fun x ctx ->
  let (_,a,_) = List.find (fun (y,_,_) -> Bindlib.eq_vars x y) ctx in a

(** [def_of x ctx] returns the definition of [x] in the context [ctx] if it
    appears, and [None] otherwise *)
let rec def_of : term Bindlib.var -> ctxt -> ctxt * term option =
  fun x ctx ->
  match ctx with
  | []         -> [], None
  | (y,_,d)::l -> if Bindlib.eq_vars x y then l,d else def_of x l

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> ctxt -> bool = fun x ->
  List.exists (fun (y,_,_) -> Bindlib.eq_vars x y)

(** [to_prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. It returns the number of products as well. *)
let to_prod : ctxt -> term -> term * int = fun ctx t ->
  let fn (t,c) elt =
    match elt with
    | (x,a,None   ) -> (_Prod (lift a) (Bindlib.bind_var x t), c + 1)
    | (x,a,Some(u)) -> (_LLet (lift a) (lift u) (Bindlib.bind_var x t), c)
  in
  let (t, c) = List.fold_left fn (lift t, 0) ctx in
  (Bindlib.unbox t, c)

(** [to_abst ctx t] builds a sequence of abstractions over the context [ctx],
    in the term [t]. It returns the number of products as well. *)
let to_abst : ctxt -> term -> term * int = fun ctx t ->
  let fn (t,c) elt =
    match elt with
    | (x,a,None   ) -> (_Abst (lift a) (Bindlib.bind_var x t), c + 1)
    | (x,a,Some(u)) -> (_LLet (lift a) (lift u) (Bindlib.bind_var x t), c)
  in
  let (t, c) = List.fold_left fn (lift t, 0) ctx in
  (Bindlib.unbox t, c)

(** [to_let ctx t] adds the defined variables of [ctx] on top of [t]. *)
let to_let : ctxt -> term -> term = fun ctx t ->
  let f t = function
    | _, _, None -> t
    | x, a, Some u -> _LLet (lift a) (lift u) (Bindlib.bind_var x t)
  in
  Bindlib.unbox (List.fold_left f (lift t) ctx)

(** [sub ctx vs] returns the sub-context of [ctx] made of the variables of
    [vs]. *)
let sub : ctxt -> tvar array -> ctxt = fun ctx vs ->
  let f ((x,_,_) as hyp) ctx =
    if Array.exists (Bindlib.eq_vars x) vs then hyp::ctx else ctx
  in
  List.fold_right f ctx []

(** [unfold ctx t] behaves like {!val:Term.unfold t} unless term[t] is of the
    form [Vari(x)] with [x] defined in [ctx]. In this case, [t] is replaced by
    the definition of [x] in [ctx].  In particular, if no operation is carried
    out on [t], we have [unfold ctx t == t]. *)
let rec unfold : ctxt -> term -> term = fun ctx t ->
  match t with
  | Meta(m, ts) ->
      begin
        match !(m.meta_value) with
        | None    -> t
        | Some(b) -> unfold ctx (Bindlib.msubst b ts)
      end
  | TEnv(TE_Some(b), ts) -> unfold ctx (Bindlib.msubst b ts)
  | TRef(r) ->
      begin
        match !r with
        | None    -> t
        | Some(v) -> unfold ctx v
      end
  | Vari(x) ->
      begin
        match def_of x ctx with
        | _, None -> t
        | ctx', Some t -> unfold ctx' t
      end
  | _ -> t

(** [get_args ctx t] decomposes term [t] as {!val:LibTerm.get_args} does, but
    any variable encountered is replaced by its definition in [ctx] (if it
    exists). *)
let get_args : ctxt -> term -> term * term list = fun ctx t ->
  let rec get_args acc t =
    match unfold ctx t with
    | Appl(t,u)    -> get_args (u::acc) t
    | t            -> (t, acc)
  in
  get_args [] t

(** {b NOTE} that both [unfold] and [get_args] redefine the functions in
    {!module:LibTerm} and {!module:Term}. *)
