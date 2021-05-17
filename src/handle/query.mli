open Core
open Term
open Parsing.Syntax
open Common.Pos
open Proof

(** [infer pos p c t] returns a type for the term [t] in context [c] and under
   the constraints of [p] if there is one, or
@raise Fatal. [c] must well sorted. Note that [p] gets modified. *)
val infer : popt -> problem -> ctxt -> term -> term

(** [check pos p c t a] checks that the term [t] has type [a] in context [c]
and under the constraints of [p], or
@raise Fatal. [c] must well sorted. Note that [p] gets modified. *)
val check : popt -> problem -> ctxt -> term -> term -> unit

(** [check_sort pos p c t] checks that the term [t] has type [Type] or [Kind]
   in context [c] and under the constraints of [p], or
@raise Fatal. [c] must be well sorted. *)
val check_sort : popt -> problem -> ctxt -> term -> unit

(** [goals_of_typ p typ ter] adds to [p] the constraints for [typ] to be of
   type a sort and [ter] to be of type [typ], and returns a type for [ter]. *)
val goals_of_typ : problem -> term loc option -> term loc option -> term

(** Result of query displayed on hover in the editor. *)
type result = (unit -> string) option

(** [handle_query ss ps q] *)
val handle : Sig_state.t -> proof_state option -> p_query -> result
