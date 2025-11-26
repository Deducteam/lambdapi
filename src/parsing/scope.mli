(** Scoping. Convert parsed terms in core terms by finding out which
   identifiers are bound variables or function symbol declared in open
   modules. *)

open Core open Sig_state open Term open Env
open Syntax

(** [scope_term ~find_sym ~typ ~mok prv ss env t] turns a pterm [t] into a
    term in the signature state [ss] and environment [env] (for bound
    variables). If [prv] is [true], then the term must not
    contain any private subterms. If [~typ] is [true], then [t] must be
    a type (defaults to [false]). No {b new} metavariables may appear in
    [t], but metavariables in the image of [mok] may be used. The function
    [mok] defaults to the function constant to [None]. The function
    [~find_sym] is used to scope symbol identifiers. *)
val scope_term :
  ?find_sym:find_sym -> ?typ:bool (* default: false *) ->
  ?mok:(int -> meta option) -> bool -> sig_state -> env -> p_term -> term

(** [scope_search_pattern ~find_sym ~typ prv ss env t] turns a pterm [t] meant
    to be a search patter into a term in the signature state [ss]
    and environment [env] (for bound variables). If [~typ] is [true],
    then [t] must be a type (defaults to [false]). No {b new} metavariables
    may appear in [t], but metavariables in the image of [mok] may be used.
    The function [mok] defaults to the function constant to [None]. The
    function [~find_sym] is used to scope symbol identifiers. *)
val scope_search_pattern :
  ?find_sym:find_sym -> ?typ:bool -> ?mok:(int -> meta option) ->
  sig_state -> env -> p_term -> term

(** [scope_rule ~find_sym ur ss r] turns a parser-level rewriting rule [r],
    or a unification rule if [ur] is true, into a pre-rewriting rule.
    The function [~find_sym] is used to scope symbol identifiers. *)
val scope_rule :
 ?find_sym: find_sym -> bool -> sig_state -> p_rule -> sym_rule

(** [scope_rwpatt ss env t] turns a parser-level rewrite tactic specification
    [s] into an actual rewrite specification (possibly containing variables of
    [env] and using [ss] for aliasing). *)
val scope_rwpatt : sig_state -> env -> p_rwpatt -> (term, binder) rwpatt
