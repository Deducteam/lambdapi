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

(** [find x ctx] returns the type of [x] in the context [ctx] when it appears,
    and raises [Not_found] otherwise. *)
let find : tvar -> t -> term = fun x ctx ->
  snd (List.find (fun (y,_) -> Bindlib.eq_vars x y) ctx)
