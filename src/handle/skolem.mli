open Common
open Core
open Term
open Fol

(** [nnf_of cfg phi] computes the negation normal form of first order formula
    [phi]. *)
val nnf_of : config -> term -> term

(** Raised by [prenex_of] when its formula is not in negation normal form. *)
exception PrenexFormulaNotNnf of term

(** [prenex_of cfg phi] computes the prenex normal form of first order formula
    [phi].
    @raise PrenexFormulaNotNnf when formula [phi] is not in negation normal
      form. *)
val prenex_of : config -> term -> term

(** [handle ss pos t] returns a skolemized form of term [t] (at position
    [pos]).  A term is skolemized when it has no existential quantifiers: to
    this end, for each existential quantifier in [t], signature state [ss] is
    extended with a new symbol in order to substitute the variable bound by
    the said quantifier. *)
val handle : Sig_state.t -> Pos.popt -> term -> term
