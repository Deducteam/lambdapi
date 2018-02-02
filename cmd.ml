(** Commands. *)

open Files
open Terms

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
  (** Type-checking command. *)
  | Check  of term * term
  (** Type inference command. *)
  | Infer  of term
  (** Normalisation command. *)
  | Eval   of term
  (** Convertibility command. *)
  | Conv   of term * term
  (** Unimplemented command. *)
  | Other  of string
