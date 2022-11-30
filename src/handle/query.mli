(** Handling of queries. *)

open Core open Term
open Parsing open Syntax
open Common open Pos
open Proof

(** [infer pos p c t] returns a couple [(t',a)] where [a] is the type of [t]
    in context [c] and under constraints of problem [p]; and [t'] is the
    refinement of [t]. Note that [p] gets modified. Context [c] must well
    sorted.
    @raise Fatal if [t] cannot be typed. *)
val infer : popt -> problem -> ctxt -> term -> term * term

(** [check pos p c t a] checks that the term [t] has type [a] in context [c]
    and under the constraints of [p], and returns [t] refined. Context [c]
    must be well-sorted. Note that [p] is modified.
    @raise Fatal if [t] is not of type [a]. *)
val check : popt -> problem -> ctxt -> term -> term -> term

(** [check_sort pos p c t] checks that the term [t] has type [Type] or [Kind]
    in context [c] and under the constraints of [p]. Context [c] must be well
    sorted.
    @raise Fatal if [t] cannot be typed by a sort (Type or Kind). *)
val check_sort : popt -> problem -> ctxt -> term -> term * term

(** Result of query displayed on hover in the editor. *)
type result = (unit -> string) option

(** [handle_query ss ps q] *)
val handle : Sig_state.t -> proof_state option -> p_query -> result
