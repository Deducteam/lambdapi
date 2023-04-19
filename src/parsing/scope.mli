(** Scoping. Convert parsed terms in core terms by finding out which
   identifiers are bound variables or function symbol declared in open
   modules. *)

open Core open Sig_state open Term open Env
open Syntax
open Common open Pos

(** [scope ~find_sym ~typ ~mok prv ss env t] turns a pterm [t] into a
    term in the signature state [ss] and environment [env] (for bound
    variables). If [prv] is [true], then the term must not
    contain any private subterms. If [~typ] is [true], then [t] must be
    a type (defaults to [false]). No {b new} metavariables may appear in
    [t], but metavariables in the image of [mok] may be used. The function
    [mok] defaults to the function constant to [None]. The function
    [~find_sym] is used to scope symbol identifiers. *)
val scope_term :
  ?find_sym:find_sym ->
  ?typ:bool (* default: false *) ->
  ?mok:(int -> meta option) ->
  bool -> sig_state -> env -> p_term -> term

(** [scope ~find_sym ~typ prv ss env t] turns a pterm [t] meant to
    be a lhs of a rewrite rule into a term in the signature state [ss]
    and environment [env] (for bound variables). If [prv] is [true], then
    the term must not contain any private subterms. If [~typ] is [true],
    then [t] must be a type (defaults to [false]). No {b new} metavariables
    may appear in [t]. The function [~find_sym] is used to scope symbol
    identifiers. *)
val scope_lhs :
  ?find_sym:find_sym ->
  ?typ:bool ->
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

(** [scope_rule ~find_sym ur ss r] turns a parser-level rewriting rule [r],
    or a unification rule if [ur] is true, into a pre-rewriting rule.
    The function [~find_sym] is used to scope symbol identifiers. *)
val scope_rule :
 ?find_sym:find_sym -> bool -> sig_state -> p_rule -> pre_rule loc

(** [scope_rw_patt ss env t] turns a parser-level rewrite tactic specification
    [s] into an actual rewrite specification (possibly containing variables of
    [env] and using [ss] for aliasing). *)
val scope_rw_patt : sig_state -> env -> p_rw_patt -> (term, tbinder) rw_patt
