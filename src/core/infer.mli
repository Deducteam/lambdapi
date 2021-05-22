open Term

(** Module that provide a lookup function to the refiner. *)
module type LOOKUP = sig
  val coercions : Sign.coercion list
  val solve : problem -> bool
  (** [solve] is a solver as specified in {!module:Unif} (see
      {!val:Unif.solve_noexn}). *)
end

module type S = sig
  exception NotTypable
  (** Raised when a term cannot be typed. *)

  val infer_noexn : problem -> ctxt -> term -> (term * term) option
  (** [infer_noexn pb ctx t] returns a couple [(t', t_ty)] where [t_ty]
      is the inferred type of [t] in problem [pb] and in context [ctx];
      [t'] is [t] refined. If [t] is not typable, [None] is returned. The
      problem is updated in place. *)

  val check_noexn : problem -> ctxt -> term -> term -> term option
  (** [check_noexn pb ctx t t_ty] ensures that term [t] has type [t_ty] in
      context [ctx] and problem [pb]. It returns term [t] refined and updates
      problem [pb]. *)

  val check_sort_noexn : problem -> ctxt -> term -> (term * term) option
    (** [check_sort_noexn cs ctx t] returns a 2-uple [(t',s)] where [t']
        is [t] refined, [s] is the inferred sort of [t'], [TYPE] or [KIND].
        If [t] is not typable, [None] is returned. *)
end

module Make : functor (_: LOOKUP) -> S

module Bare : S
