(** Typing context. *)

open Extra
open Terms

(** An element of the context. *)
type hypothesis =
  | Assume of tvar * term
  (** [Assume(x,a)] assumes that variable [x] is of type [a]. *)
  | Define of {ctx_v: tvar; ctx_y: term; ctx_e: term}
  (** [Define{ctx_v=x,ctx_y=a,ctx_e=t}] defines variable [x] to be term [t] of
      type [a]. *)

(** Representation of a typing context, associating a type or term with type
    to free [Bindlib] variables. *)
type t = hypothesis list

(** [empty] is the empty context. *)
let empty : t = []

(** [assume h ctx] adds list of assumptions [h] mapping variables to their
    types to context [ctx]. *)
let assume : (tvar * term) list -> t -> t = fun hyps ctx ->
  List.map (fun (x,a) -> Assume(x, a)) hyps @ ctx

(** [define x a t ctx] maps variable [x] to term [t] of type [a] in [ctx]. *)
let define : tvar -> term -> term -> t -> t = fun x a t ctx ->
  Define{ctx_v=x;ctx_y=a;ctx_e=t}::ctx

(** [unbind_ctxt ctx a b] returns the triple [(x,b,ctx')] such that [(x,b)]
   is the unbinding of [b] and [ctx'] is the context [ctx] extended with
   [(x,a)] if [x] occurs in [b]. *)
let unbind ctx a b =
  let (x,b') = Bindlib.unbind b in
  let ctx' = if Bindlib.binder_occur b then assume [(x,a)] ctx else ctx in
  (x,b',ctx')

(** [pp oc ctx] prints the context [ctx] to the channel [oc]. *)
let pp : t pp = fun oc ctx ->
  let pp_e oc h =
    match h with
    | Assume(x,a)                     ->
        Format.fprintf oc "%a : %a" Print.pp_tvar x Print.pp a
    | Define{ctx_v=x;ctx_y=a;ctx_e=t} ->
        Format.fprintf oc "%a : %a ≔ %a" Print.pp_tvar x Print.pp a Print.pp t
  in
  if ctx = [] then Format.pp_print_string oc "∅"
  else List.pp pp_e ", " oc (List.rev ctx)

(** [assumptions ctx] returns a list mapping free variable to their types. *)
let assumptions : t -> (tvar * term) list =
  let f hyp = match hyp with
      Assume(x,a) | Define{ctx_v=x;ctx_y=a;_} -> (x, a)
  in
  List.map f

(** [find x ctx] returns the type of [x] in the context [ctx] when it appears,
    and raises [Not_found] otherwise. *)
let type_of : tvar -> t -> term = fun x ctx ->
  let f hyp =
    match hyp with
    | Assume(y,_)
    | Define{ctx_v=y;_} when Bindlib.eq_vars x y -> true
    | _                                          -> false
  in
  match List.find f ctx with Assume(_,a) | Define{ctx_y=a;_} -> a

(** [mem x ctx] tells whether variable [x] is mapped in the context [ctx]. *)
let mem : tvar -> t -> bool = fun x ctx ->
  try ignore (type_of x ctx); false with Not_found -> true

(** [to_prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. *)
let to_prod : t -> term -> term = fun ctx t ->
  match ctx with
  | []            -> t
  | [Assume(x,a)] -> Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift t)))
  | _             ->
      let fn t hyp =
        match hyp with Assume(x,a)
                     | Define{ctx_v=x;ctx_y=a;_} ->
          _Prod (lift a) (Bindlib.bind_var x t)
      in
      Bindlib.unbox (List.fold_left fn (lift t) ctx)

(** [of_env] builds a context from an environment. **)
let of_env : Env.t -> t =
  List.map (fun (_,(v,bt)) -> Assume(v,Bindlib.unbox bt))

(** [make_meta ctx a] creates a metavariable of type [a],  with an environment
    containing the variables of context [ctx]. *)
let make_meta : t -> term -> term = fun ctx a ->
  let m = fresh_meta (to_prod ctx a) (List.length ctx) in
  let getv hyp = match hyp with Assume(v,_) | Define{ctx_v=v;_} -> Vari(v) in
  Meta(m, Array.of_list (List.rev_map getv ctx))

(** [sub ctx vs] return the sub-context of [ctx] made of the variables of
    [vs]. *)
let sub : t -> tvar array -> t = fun ctx vs ->
  let f hyp ctx =
    let v = match hyp with Define{ctx_v=x;_} | Assume(x,_) -> x in
    if Array.exists (Bindlib.eq_vars v) vs then hyp::ctx else ctx
  in
  List.fold_right f ctx []
