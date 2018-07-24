(** Parser-level representation of terms (and patterns). *)
type p_term =
  | P_Vari of string list * string
  | P_Type
  | P_Prod of string * p_term option * p_term
  | P_Abst of string * p_term option * p_term
  | P_Appl of p_term * p_term
  | P_Wild
  | P_Meta of string * p_term array

type old_p_rule = (string * p_term option) list * p_term * p_term

(** Representation of a toplevel command. *)
type p_cmd =
  (** Symbol declaration (constant when the boolean is [true]). *)
  | P_SymDecl  of bool * string * p_term
  (** Quick definition (opaque when the boolean is [true]). *)
  | P_SymDef   of bool * string * p_term option * p_term
  (** Rewriting rules declaration. *)
  | P_OldRules of old_p_rule list
  (** Require an external signature. *)
  | P_Require  of string list
  (** Type inference command. *)
  | P_Infer    of p_term * Eval.config
  (** Normalisation command. *)
  | P_Eval     of p_term * Eval.config
  (** Type-checking command. *)
  | P_TestType of bool * bool * p_term * p_term
  (** Convertibility command. *)
  | P_TestConv of bool * bool * p_term * p_term
  (** Unimplemented command. *)
  | P_Other    of string
