open Term

(** [solve_noexn ~type_check problem] attempts to solve [problem]. If there is
   no solution, the value [None] is returned. Otherwise [Some cs] is returned,
   where the list [cs] is a list of unsolved convertibility
   constraints. Metavariable instantiations are type-checked only if the
   optional argument [~type_check] is [true] (default). *)
val solve_noexn : ?type_check:bool -> problem -> bool
