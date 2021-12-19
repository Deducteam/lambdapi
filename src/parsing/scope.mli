(** Scoping. Convert parsed terms in core terms by finding out which
   identifiers are bound variables or function symbol declared in open
   modules. *)

open Core
open Sig_state
open Term
open Env
open Syntax
open Common
open Pos

(** [scope ~typ prv ss env p mok mon t] turns a pterm [t] into a term in the
   signature state [ss], the environment [env] (for bound variables). [mok k]
   says if there already exists a meta with key [k]. [mon n] says if there
   already exists a meta with name [n]. Generated metas are added to [p].
   [prv] indicates if private symbols are allowed. [typ] indicates whether [t]
   should be type (default is false). *)
val scope_term : ?typ:bool (* default: false *)
      -> bool -> sig_state -> env
      -> problem -> (int -> meta option) -> (string -> meta option)
      -> p_term -> term

(** [scope_term_with_params prv ss env p mok mon t] is similar to [scope_term
   expo ss env p mok mon t] except that [t] must be a product or an
   abstraction. In this case, no warnings are issued if the top binders are
   constant. *)
val scope_term_with_params :
      bool -> sig_state -> env
      -> problem -> (int -> meta option) -> (string -> meta option)
      -> p_term -> term

(** Representation of a rewriting rule prior to SR-checking. *)
type pre_rule =
  { pr_sym      : sym
  (** Head symbol of the LHS. *)
  ; pr_lhs      : term list
  (** Arguments of the LHS. *)
  ; pr_vars     : term_env Bindlib.mvar
  (** Pattern variables that appear in the RHS. The last [pr_xvars_nb]
      variables do not appear in the LHS. *)
  ; pr_rhs      : tbox
  (** Body of the RHS, should only be unboxed once. *)
  ; pr_names    : (int, string) Hashtbl.t
  (** Gives the original name (if any) of pattern variable at given index. *)
  ; pr_arities  : int array
  (** Gives the arity of all the pattern variables in field [pr_vars]. *)
  ; pr_xvars_nb : int
  (** Number of variables that appear in the RHS but not in the LHS. *) }

(** [rule_of_pre_rule r] converts a pre-rewrite rule into a rewrite rule. *)
val rule_of_pre_rule : pre_rule loc -> rule

(** [scope_rule ss r] turns a parser-level rewriting rule [r] into a
    pre-rewriting rule. *)
val scope_rule : sig_state -> p_rule -> pre_rule loc

(** [scope_unif_rule ss r] turns a parser-level unification rule [r] into a
    pre-rewriting rule. *)
val scope_unif_rule : sig_state -> p_rule -> pre_rule loc

(** [scope_meta_rule ss r] turns a parser-level meta rewriting rule [r]
    into a pre-rewriting rule. *)
val scope_meta_rule : sig_state -> p_rule -> pre_rule loc

(** [scope_rw_patt ss env t] turns a parser-level rewrite tactic specification
    [s] into an actual rewrite specification (possibly containing variables of
    [env] and using [ss] for aliasing). *)
val scope_rw_patt : sig_state -> env -> p_rw_patt -> (term, tbinder) rw_patt
