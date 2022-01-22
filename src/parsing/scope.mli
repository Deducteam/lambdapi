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

(** [scope ~typ ~mok prv expo ss env p t] turns a pterm [t] into a term in
    the signature state [ss] and environment [env] (for bound
    variables). If [expo] is {!constructor:Public}, then the term must not
    contain any private subterms. If [~typ] is [true], then [t] must be
    a type (defaults to [false]). No {b new} metavariables may appear in
    [t], but metavariables in the image of [mok] may be used. The function
    [mok] defaults to the function constant to [None] *)
val scope_term :
  ?typ:bool (* default: false *) ->
  ?mok:(int -> meta option) ->
  bool -> sig_state -> env -> p_term -> term

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
