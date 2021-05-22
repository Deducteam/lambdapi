open Term

(** [solve_noexn ~type_check p] tries to simplify the constraints of [p]. It
   returns [false] if it finds a constraint that cannot be
   satisfied. Otherwise, [p.to_solve] is empty but [p.unsolved] may still
   contain constraints that could not be simplified. Metavariable
   instantiations are type-checked only if [~type_check] is [true]. If
   [~type_check] is not specified, it defaults to [true]. *)
val solve_noexn : ?type_check:bool -> problem -> bool

val typechecker : ?type_check:bool -> Sign.coercion list -> (module Infer.S)
(** [typechecker cions] creates a typechecker with {!val:solve_noexn} as
    unification function from coercions [cions] and sets it as the typechecker
    used by the unification algorithm. This function should always be used to
    obtain a typechecker. *)

module Infer : Infer.S
(** A type checker with unification (but without coercions). *)
