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

(** [unbind_ctxt ctx a b] returns the triple [(x,b,ctx')] such that [(x,b)]
   is the unbinding of [b] and [ctx'] is the context [ctx] extended with
   [(x,a)] if [x] occurs in [b]. *)
let unbind ctx a b =
  let (x,b') = Bindlib.unbind b in
  let ctx' = if Bindlib.binder_occur b then add x a ctx else ctx in
  (x,b',ctx')

(** [pp oc ctx] prints the context [ctx] to the channel [oc]. *)
let pp : t pp = fun oc ctx ->
  let pp_e oc (x,a) =
    Format.fprintf oc "%a : %a" Print.pp_tvar x Print.pp a
  in
  if ctx = [] then Format.pp_print_string oc "∅"
  else List.pp pp_e ", " oc (List.rev ctx)

(** [find x ctx] returns the type of [x] in the context [ctx] when it appears,
    and raises [Not_found] otherwise. *)
let type_of : tvar -> t -> term = fun x ctx ->
  snd (List.find (fun (y,_) -> Bindlib.eq_vars x y) ctx)

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> t -> bool = fun x ctx ->
  try ignore (type_of x ctx); false with Not_found -> true

(** [to_prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. *)
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

(** [sub ctx vs] return the sub-context of [ctx] made of the variables of
    [vs]. *)
let sub : t -> tvar array -> t = fun ctx ts ->
  let f (v,t) ctx =
    if Array.exists (Bindlib.eq_vars v) ts then (v,t)::ctx else ctx
  in
  List.fold_right f ctx []
