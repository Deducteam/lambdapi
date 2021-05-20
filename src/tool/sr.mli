open Core
open Common
open Parsing

(** [check_rule r] checks whether the pre-rule [r] is well-typed in
   signature state [ss] and then construct the corresponding rule. Note that
   [Fatal] is raised in case of error. *)
val check_rule : Scope.pre_rule Pos.loc -> Term.rule
