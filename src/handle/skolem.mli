open Common
open Core
open Term

(** Builtin configuration for propositional logic. *)
type fol_config = {
  symb_P : sym;  (** Encoding of propositions. *)
  symb_T : sym;  (** Encoding of types. *)
  symb_or : sym;  (** Disjunction(∨) symbol. *)
  symb_and : sym;  (** Conjunction(∧) symbol. *)
  symb_imp : sym;  (** Implication(⇒) symbol. *)
  symb_bot : sym;  (** Bot(⊥) symbol. *)
  symb_top : sym;  (** Top(⊤) symbol. *)
  symb_not : sym;  (** Not(¬) symbol. *)
  symb_ex : sym;  (** Exists(∃) symbol. *)
  symb_all : sym;  (** Forall(∀) symbol. *)
}

(** [nnf_of cfg phi] computes the negation normal form of first order formula
    [phi]. *)
val nnf_of : fol_config -> term -> term

(** Raised by [prenex_of] when its formula is not in negation normal form. *)
exception PrenexFormulaNotNnf of term

(** [prenex_of cfg phi] computes the prenex normal form of first order formula
    [phi].
    @raise PrenexFormulaNotNnf when formula [phi] is not in negation normal
      form. *)
val prenex_of : fol_config -> term -> term

(** [handle ss pos t] returns a skolemized form of term [t] (at position
    [pos]).  A term is skolemized when it has no existential quantifiers: to
    this end, for each existential quantifier in [t], signature state [ss] is
    extended with a new symbol in order to substitute the variable bound by
    the said quantifier. *)
val handle : Sig_state.t -> Pos.popt -> term -> term
