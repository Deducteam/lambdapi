open Common
open Core
open Term
open Fol

(** [nnf cfg phi] returns the negation normal form of [phi], assuming it is
    the encoding of a first-order formula using [cfg]. *)
val nnf : config -> term -> term

exception NotInNnf of term

(** [pnf cfg phi] returns the prenex normal form of [phi].
    @raise NotInNnf when formula [phi] is not in negation normal form. *)
val pnf : config -> term -> term

(** [skolem ss pos t] returns the skolemized form of [t] ([pos] is used for
    error messages). Existential quantifiers are replaced by new symbols that
    are added in the signature state [ss]. *)
val handle : Sig_state.t -> Pos.popt -> term -> term
