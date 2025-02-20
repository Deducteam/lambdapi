(** Checking that a rule preserves typing (subject reduction property). *)

open Core open Term
open Common

(** [check_rule r] checks whether the pre-rule [r] is well-typed in
   signature state [ss] and then construct the corresponding rule. Note that
   [Fatal] is raised in case of error. *)
val check_rule : Pos.popt -> sym_rule -> sym_rule
