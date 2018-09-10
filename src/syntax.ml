open Files
open Pos

(** Type of a (located) identifier. *)
type ident = strloc

(** Type of a (qualified) identifier. *)
type qident = module_path * ident

(** Symbol tag. *)
type symtag =
  | Sym_const
  | Sym_inj

(** Parser-level term representation. *)
type p_term = p_term_aux Pos.loc
and p_term_aux =
  | P_Type
  | P_Vari of qident
  | P_Wild
  | P_Meta of strloc * p_term array
  | P_Patt of strloc * p_term array
  | P_Appl of p_term * p_term
  | P_Impl of p_term * p_term
  | P_Abst of p_arg list * p_term
  | P_Prod of p_arg list * p_term

(** Synonym of [p_term] for semantic hints. *)
and p_type = p_term

(** Parser-level representation of a function argument. *)
and p_arg = ident * p_type option

(** Parser-level rewriting rule representation. *)
type p_rule = p_term * p_term

(** Parser-level representation of a proof tactic. *)
type p_tactic =
  | P_tac_intro  of ident list
  | P_tac_refine of p_term
  (* TODO *)

(** Parserl-level representation of a proof terminator. *)
type p_proof_end =
  | Proof_QED
  | Proof_admit
  | Proof_abort

(** Parser-level representation of an assertion. *)
type p_assertion =
  | P_assert_typing of p_term * p_term
  | P_assert_conv   of p_term * p_term

(** Parser-level representation of a configuration command. *)
type p_config =
  | P_verbose of int
  | P_debug   of bool * string

(** Parser-level representation of a single command. *)
type p_cmd =
  | P_req    of bool * module_path
  (** Require statement (opened if boolean is [true]). *)
  | P_req_as of module_path * ident
  (** Require statement with alias (renaming). *)
  | P_open   of module_path
  (** Open statement. *)
  | P_symbol of symtag list * ident * p_type
  (** Symbol declaration. *)
  | P_rules  of p_rule list
  (** Rewriting rule declarations. *)
  | P_def    of ident * p_arg list * p_type option * p_term
  (** Definition of a symbol (unfoldable). *)
  | P_thm    of ident * p_type * p_tactic list * p_proof_end
  (** Theorem with its proof. *)
  | P_assert of bool * p_assertion
  (** Assertion (must fail if boolean is [true]). *)
  | P_set    of p_config
  (** Set the configuration (debug, logging, ...). *)
