(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = out_channel -> 'a -> unit

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

module List =
  struct
    include List

    (** [pp pp_e sep oc l] prints the list [l] on the channel [oc] using [sep]
        as separator, and [pp_e] for printing the elements. *)
    let pp : 'a pp -> string -> 'a list pp = fun pp_elt sep oc l ->
      match l with
      | []    -> ()
      | e::es -> let fn e = Printf.fprintf oc "%s%a" sep pp_elt e in
                 pp_elt oc e; iter fn es
  end

module Array =
  struct
    include Array

    (** [for_all2 p a1 a2] checks if the corresponding elements of arrays [a1]
        and [a2] satisfy the predicate [p].  The [Invalid_argument]  exception
        is raised if the arrays do not have the same size. *)
    let for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool =
      fun f a1 a2 ->
        let f x y = if not (f x y) then raise Exit in
        try iter2 f a1 a2; true with Exit -> false

    (** [pp pp_e sep oc a] prints the array list [a] on the channel [oc] using
        [sep] as separator, and [pp_e] for printing the elements. *)
    let pp : 'a pp -> string -> 'a array pp = fun pp_elt sep oc a ->
      List.pp pp_elt sep oc (to_list a)
  end

module Bindlib =
  struct
    include Bindlib

    (* [eq_binder eq b1 b2] tests the equality of two binders [b1] and [b2] by
       substituting them with the same free variable, and testing the equality
       of the obtained values with the [eq] function. *)
    let eq_binder : ('a var -> 'a) -> 'b eq -> ('a,'b) Bindlib.binder eq =
      fun mkfree eq f g -> f == g ||
        let x = mkfree (new_var mkfree "_eq_binder_") in
        eq (subst f x) (subst g x)
  end
