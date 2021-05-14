open Term

(** Given a meta [m] of type [Πx1:a1,..,Πxn:an,b], [set_to_prod p m] sets [m]
   to a product term of the form [Πy:m1[x1;..;xn],m2[x1;..;xn;y]] with fresh
   metavariables [m1] and [m2], and updates the metas of the problem [p]. *)
val set_to_prod : problem -> meta -> unit

(** [infer_noexn p ctx t] returns [None] if the type of [t] in context [ctx]
   cannot be infered, or [Some a] where [a] is some type of [t] in the context
   [ctx] if the constraints [p.to_solve] are satisfiable (which may not be the
   case). The metavariables of [p] are updated when a metavariable is
   instantiated or created. [ctx] must be well sorted. *)
val infer_noexn : problem -> ctxt -> term -> term option

(** [check_noexn p ctx t a] tells whether the term [t] has type [a] in the
   context [ctx] if the returned constraints [p.to_solve] are satisfiable. The
   metavariables of [p] are updated when a metavariable is instantiated or
   created. New constraints may be added as well. The context [ctx] and the
   type [a] must be well sorted. *)
val check_noexn : problem -> ctxt -> term -> term -> bool
