(** Typing context. *)

open Term
open Lplib
open Timed

(** [type_of x ctx] returns the type of [x] in the context [ctx] when it
    appears in it, and
@raise [Not_found] otherwise. *)
let type_of : tvar -> ctxt -> term = fun x ctx ->
  let (_,a,_) = List.find (fun (y,_,_) -> Bindlib.eq_vars x y) ctx in a

(** [def_of x ctx] returns the definition of [x] in the context [ctx] if it
    appears, and [None] otherwise *)
let rec def_of : tvar -> ctxt -> ctxt * term option = fun x c ->
  match c with
  | []         -> [], None
  | (y,_,d)::c -> if Bindlib.eq_vars x y then c,d else def_of x c

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> ctxt -> bool = fun x ->
  List.exists (fun (y,_,_) -> Bindlib.eq_vars x y)

(** [to_prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. It returns the number of products as well. *)
let to_prod : ctxt -> term -> term * int = fun ctx t ->
  let f (t,c) (x,a,v) =
    let b = Bindlib.bind_var x t in
    match v with
    | None -> _Prod (lift a) b, c + 1
    | Some v -> _LLet (lift a) (lift v) b, c
  in
  let t, c = List.fold_left f (lift t, 0) ctx in
  Bindlib.unbox t, c

(** [to_prod_box bctx t] is similar to [to_prod bctx t] but operates on boxed
    contexts and terms. *)
let to_prod_box : bctxt -> tbox -> tbox * int = fun bctx t ->
  let f (t, c) (x, a) =
    let b = Bindlib.bind_var x t in
    (_Prod a b, c + 1)
  in
  List.fold_left f (t, 0) bctx

(** [box_context ctx] lifts context [ctx] to a boxed context. *)
let box_context : ctxt -> bctxt =
  List.filter_map
    (fun (x, t, u) -> if u = None then Some (x, lift t) else None)

(** [to_abst ctx t] builds a sequence of abstractions over the context [ctx],
    in the term [t]. *)
let to_abst : ctxt -> term -> term = fun ctx t ->
  let f t (x, a, _) = _Abst (lift a) (Bindlib.bind_var x t) in
  Bindlib.unbox (List.fold_left f (lift t) ctx)

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

(** [unfold ctx t] behaves like {!val:Term.unfold} unless term [t] is of the
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

(** [get_args ctx t] decomposes term [t] as {!val:Term.get_args} does, but
    any variable encountered is replaced by its definition in [ctx] (if it
    exists). *)
let get_args : ctxt -> term -> term * term list = fun ctx t ->
  let rec get_args acc t =
    match unfold ctx t with
    | Appl(t,u)    -> get_args (u::acc) t
    | t            -> (t, acc)
  in
  get_args [] t

(** [to_map] builds a map from a context. *)
let to_map : ctxt -> term VarMap.t =
  let add_def m (x,_,v) =
    match v with Some v -> VarMap.add x v m | None -> m
  in List.fold_left add_def VarMap.empty
