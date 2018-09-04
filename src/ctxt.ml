(** Typing context. *)

open Extra
open Terms

(** Representation of a typing context, associating a type (or [Term.term]) to
    free [Bindlib] variables. *)
type t = (tvar * term) list

(** [empty] is the empty context. *)
let empty : t = []

(** [add x a ctx] maps the variable [x] to the type [a] in [ctx]. *)
let add : tvar -> term -> t -> t =
  fun x a ctx -> (x,a)::ctx

(** [pp oc ctx] prints the context [ctx] to the channel [oc]. *)
let pp : t pp = fun oc ctx ->
  let pp_e oc (x,a) =
    Format.fprintf oc "%a : %a" Print.pp_tvar x Print.pp a
  in
  if ctx = [] then Format.pp_print_string oc "∅"
  else List.pp pp_e ", " oc (List.rev ctx)

(** [find x ctx] returns the type of [x] in the context [ctx] when it appears,
    and raises [Not_found] otherwise. *)
let find : tvar -> t -> term = fun x ctx ->
  snd (List.find (fun (y,_) -> Bindlib.eq_vars x y) ctx)

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> t -> bool = fun x ctx ->
  try ignore (find x ctx); false with Not_found -> true

(** [unbind ctx a b] substitutes the binder [b] with a fresh variable [x], and
    extends [ctx] with the binding [(x,a)]. When [x] does not occur, the [ctx]
    is not extended. *)
let unbind : t -> term -> tbinder -> t * term = fun ctx a b ->
  let occurs = Bindlib.binder_occur b in
  let (x,b) = Bindlib.unbind b in
  if occurs then (add x a ctx, b) else (ctx, b)

(** [unbind2 ctx a b1 b2] is similar to [unbind], but it handle two binders at
    once. They are substituted with the same, fresh variable. *)
let unbind2 : t -> term -> tbinder -> tbinder -> t * term * term =
  fun ctx a b1 b2 ->
    let occurs = Bindlib.binder_occur b1 || Bindlib.binder_occur b2 in
    let (x,b1,b2) = Bindlib.unbind2 b1 b2 in
    let c = if occurs then add x a ctx else ctx in
    (c, b1, b2)

(** [to_prod ctx t] builds a product type by abstracting over the context [ctx]
    in the term [t]. *)
let to_prod : t -> term -> term = fun ctx t ->
  match ctx with
  | []      -> t
  | [(x,a)] -> Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift t)))
  | _       -> let fn t (x,a) = _Prod (lift a) (Bindlib.bind_var x t) in
               Bindlib.unbox (List.fold_left fn (lift t) ctx)

(** [of_env] builds a context from an environment. **)
let of_env : Env.t -> t =
  List.map (fun (_,(v,bt)) -> v,Bindlib.unbox bt)

(** [make_meta ctx a] creates a metavariable of type [a],  with an environment
    containing the variables of context [ctx]. *)
let make_meta : t -> term -> term = fun ctx a ->
  let m = fresh_meta (to_prod ctx a) (List.length ctx) in
  Meta(m, Array.of_list (List.rev_map (fun (v,_) -> Vari v) ctx))
