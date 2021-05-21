open Term

(** [solve_noexn ~type_check p] tries to simplify the constraints of [p]. It
   returns [false] if it finds a constraint that cannot be
   satisfied. Otherwise, [p.to_solve] is empty but [p.unsolved] may still
   contain constraints that could not be simplified. Metavariable
   instantiations are type-checked only if [~type_check] is [true]. If
   [~type_check] is not specified, it defaults to [true]. *)
val solve_noexn : ?type_check:bool -> problem -> bool
