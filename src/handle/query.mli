open Core
open Term
open Parsing.Syntax
open Common.Pos
open Proof

(** [infer pos ctx t] returns a type for [t] in context [ctx] if there
   is one.
@raise Fatal otherwise. [ctx] must well sorted. *)
val infer : popt -> problem -> ctxt -> term -> term

(** [check pos ctx t a] checks that [t] has type [a] in context [ctx].
@raise Fatal otherwise. [ctx] must well sorted. *)
val check : popt -> problem -> ctxt -> term -> term -> unit

(** [check_sort pos ctx t] checks that [t] has type [Type] or [Kind] in
   context [ctx].
@raise Fatal otherwise. [ctx] must well sorted. *)
val check_sort : popt -> problem -> ctxt -> term -> unit

(** [goals_of_typ typ ter] returns the list of unification goals that must be
    solved so that [typ] is typable by a sort and [ter] has type [typ]. *)
val goals_of_typ : problem -> term loc option -> term loc option -> term

(** Result of query displayed on hover in the editor. *)
type result = (unit -> string) option

(** [handle_query ss ps q] *)
val handle : Sig_state.t -> proof_state option -> p_query -> result
