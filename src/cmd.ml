(** Commands. *)

open Files
open Terms
open Pos

(** Type of the tests that can be made in a file. *)
type test_type =
  | Convert of term * term (** Convertibility test. *)
  | HasType of term * term (** Type-checking. *)

type test =
  { is_assert : bool (** Should the program fail if the test fails? *)
  ; must_fail : bool (** Is this test supposed to fail? *)
  ; contents  : test_type  (** The test itself. *) }

(** Representation of a toplevel command. *)
type cmd = cmd_aux loc
 and cmd_aux =
  (** Static symbol declaration. *)
  | NewSym of strloc * term
  (** Definable symbol declaration. *)
  | NewDef of strloc * term
  (** Rewriting rules declaration. *)
  | Rules  of (def * rule) list
  (** Quick definition. *)
  | Def    of bool * strloc * term * term
  (** Import an external signature. *)
  | Import of module_path
  (** Set debugging flags. *)
  | Debug  of bool * string
  (** Set the verbosity level. *)
  | Verb   of int
  (** Type inference command. *)
  | Infer  of term * Eval.config
  (** Normalisation command. *)
  | Eval   of term * Eval.config
  (** Test command. *)
  | Test   of test
  (** Unimplemented command. *)
  | Other  of strloc
