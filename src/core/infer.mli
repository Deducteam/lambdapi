(** Type inference and checking *)

open Term

(** [solve] may be set to any unification algorithm that answers [true]
    if a problem is solvable and false otherwise. A reference is used
    to avoid functorising the typechecker. *)
val solve: (problem -> bool) Timed.ref

(** [infer_noexn p ctx t] returns [None] if the type of [t] in context [ctx]
   cannot be inferred, or [Some a] where [a] is some type of [t] in the
   context [ctx], possibly adding new constraints in [p]. The metavariables of
   [p] are updated when a metavariable is instantiated or created. [ctx] must
   be well sorted. *)
val infer_noexn : problem -> ctxt -> term -> (term * term) option

(** [check_noexn p ctx t a] tells whether the term [t] has type [a] in the
   context [ctx], possibly adding new constraints in [p]. The metavariables of
   [p] are updated when a metavariable is instantiated or created. The context
   [ctx] and the type [a] must be well sorted. *)
val check_noexn : problem -> ctxt -> term -> term -> term option

val check_sort_noexn : problem -> ctxt -> term -> (term * term) option
