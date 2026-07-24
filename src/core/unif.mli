(** Solving unification constraints. *)

open Term

(** [instantiate p c m ts u] checks whether, with a constraint [m[ts] ≡ u],
   [m] can be instantiated and, if so, instantiates it and updates the
   metavariables of [p]. *)
val instantiate : problem -> ctxt -> meta -> term array -> term -> bool

(** [solve_noexn ~print ~type_check p] tries to simplify the constraints of
    [p]. It returns [false] if it finds a constraint that cannot be
    satisfied. Otherwise, [p.to_solve] is empty but [p.unsolved] may still
    contain constraints that could not be simplified. Metavariable
    instantiations are type-checked only if [~type_check] is [true]
    (default). Error messages are generated only if [~print] is [true]
    (default). *)
val solve_noexn : ?print:bool -> ?type_check:bool -> problem -> bool
