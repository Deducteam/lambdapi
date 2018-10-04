(** Parser-level abstract syntax. *)

open Console
open Files
open Pos

(** Representation of a (located) identifier. *)
type ident = strloc

(** Representation of a possibly qualified (and located) identifier. *)
type qident = (module_path * string) Pos.loc

(** Parser-level (located) term representation. *)
type p_term = p_term_aux Pos.loc
and p_term_aux =
  | P_Type
  (** TYPE constant. *)
  | P_Vari of qident
  (** Variable (empty module path) or symbol (arbitrary module path). *)
  | P_Wild
  (** Wildcard (place-holder for terms). *)
  | P_Meta of strloc * p_term array
  (** Meta-variable with the given environment. *)
  | P_Patt of strloc * p_term array
  (** Higher-order pattern (used for rules LHS / RHS). *)
  | P_Appl of p_term * p_term
  (** Application. *)
  | P_Impl of p_term * p_term
  (** Implication. *)
  | P_Abst of p_arg list * p_term
  (** Abstraction over several variables. *)
  | P_Prod of p_arg list * p_term
  (** Product over several variables. *)
  | P_LLet of strloc * p_arg list * p_term * p_term
  (** Local let. *)
  | P_NLit of int
  (** Natural number literal. *)

(** Synonym of [p_term] for semantic hints. *)
and p_type = p_term

(** Synonym of [p_term] for semantic hints. *)
and p_patt = p_term

(** Parser-level representation of a function argument. *)
and p_arg = ident * p_type option

(** Representation of a symbol tag. *)
type symtag =
  | Sym_const
  (** The symbol is constant. *)
  | Sym_inj
  (** The symbol is injective. *)

(** Parser-level rewriting rule representation. *)
type p_rule = (p_patt * p_term) Pos.loc

(** Rewrite pattern specification. *)
type p_rw_patt =
  | P_rw_Term           of p_term
  | P_rw_InTerm         of p_term
  | P_rw_InIdInTerm     of ident * p_term
  | P_rw_IdInTerm       of ident * p_term
  | P_rw_TermInIdInTerm of p_term * ident * p_term
  | P_rw_TermAsIdInTerm of p_term * ident * p_term

(** Parser-level representation of a proof tactic. *)
type p_tactic_aux =
  | P_tac_refine  of p_term
  (** Refine the current goal using the given term. *)
  | P_tac_intro   of ident list
  (** Eliminate quantifiers using the given names for hypotheses. *)
  | P_tac_apply   of p_term
  (** Apply the given term to the current goal. *)
  | P_tac_simpl
  (** Normalize in the focused goal. *)
  | P_tac_rewrite of p_rw_patt loc option * p_term
  (** Apply rewriting using the given lemma and pattern. *)
  | P_tac_refl
  (** Apply reflexivity of equality. *)
  | P_tac_sym
  (** Apply symmetry of equality. *)
  | P_tac_focus   of int
  (** Focus on the given goal. *)
  | P_tac_print
  (** Print the current goal. *)
  | P_tac_proofterm
  (** Print the current proof term (possibly containing open goals). *)
type p_tactic = p_tactic_aux Pos.loc

(** Parser-level representation of a proof terminator. *)
type p_proof_end =
  | P_proof_QED
  (** The proof is done and fully checked. *)
  | P_proof_admit
  (** Give up current state and admit the theorem. *)
  | P_proof_abort
  (** Abort the proof (theorem not admitted). *)

(** Parser-level representation of an assertion. *)
type p_assertion =
  | P_assert_typing of p_term * p_type
  (** The given term should have the given type. *)
  | P_assert_conv   of p_term * p_term
  (** The two given terms should be convertible. *)

(** Parser-level representation of a configuration command. *)
type p_config =
  | P_config_verbose of int
  (** Sets the verbosity level. *)
  | P_config_debug   of bool * string
  (** Toggles logging functions described by string according to boolean. *)
  | P_config_builtin of string * qident
  (** Sets the configuration for a builtin syntax (e.g., nat literals). *)

type require_mode =
  | P_require_default
  (** Just require the module. *)
  | P_require_open
  (** Require the module and open it. *)
  | P_require_as of ident
  (** Require the module and aliases it with the given indentifier. *)

(** Parser-level representation of a single command. *)
type p_cmd =
  | P_require    of module_path * require_mode
  (** Require statement. *)
  | P_open       of module_path
  (** Open statement. *)
  | P_symbol     of symtag list * ident * p_type
  (** Symbol declaration. *)
  | P_rules      of p_rule list
  (** Rewriting rule declarations. *)
  | P_definition of ident * p_arg list * p_type option * p_term
  (** Definition of a symbol (unfoldable). *)
  | P_theorem    of ident * p_type * p_tactic list * p_proof_end
  (** Theorem with its proof. *)
  | P_assert     of bool * p_assertion
  (** Assertion (must fail if boolean is [true]). *)
  | P_set        of p_config
  (** Set the configuration (debug, logging, ...). *)
