(** Commands. *)

open Files
open Terms

(** Type of the tests that can be made in a file. *)
type test_type =
  | Convert of term * term (** Convertibility test. *)
  | HasType of term * term (** Type-checking. *)

type test =
  { is_assert : bool (** Should the program fail if the test fails? *)
  ; must_fail : bool (** Is this test supposed to fail? *)
  ; contents  : test_type  (** The test itself. *) }

(** Representation of a toplevel command. *)
type cmd =
  (** Static symbol declaration. *)
  | NewSym of string * term
  (** Definable symbol declaration. *)
  | NewDef of string * term
  (** Rewriting rules declaration. *)
  | Rules  of (Ctxt.t * def * term * term * rule) list
  (** Quick definition. *)
  | Def    of bool * string * term * term
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
  | Other  of string
