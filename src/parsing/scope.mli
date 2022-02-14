(** Scoping. Convert parsed terms in core terms by finding out which
   identifiers are bound variables or function symbol declared in open
   modules. *)

open Core open Sig_state open Term open Env
open Syntax

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

(** [scope_rule ur ss r] turns a parser-level rewriting rule [r], or a
    unification rule if [ur] is true, into a pre-rewriting rule. *)
val scope_rule : bool -> sig_state -> p_rule -> sym_rule

(** [scope_rw_patt ss env t] turns a parser-level rewrite tactic specification
    [s] into an actual rewrite specification (possibly containing variables of
    [env] and using [ss] for aliasing). *)
val scope_rw_patt : sig_state -> env -> p_rw_patt -> (term, tbinder) rw_patt
