(** Evaluation and conversion.

Preliminary remarks. We define the head-structure of a term t as:
- λx:_,h if t=λx:a,u and h is the head-structure of u
- Π if t=Πx:a,u
- h _ if t=uv and h is the head-structure of u
- ? if t=?M.[t1;...;tn] (and ?M is not instantiated)
- t itself otherwise (TYPE, KIND, x, f)

A term t is in head-normal form (hnf) if its head-structure is invariant by
reduction.

A term t is in weak head-normal form (whnf) if it is an abstraction or if it
is in hnf. In particular, a term in head-normal form is in weak head-normal
form.

A term t is in strong normal form (snf) if it cannot be reduced further. *)

open Term

(** Flag indicating whether eta-reduction should be used or not. *)
val eta_equality : bool Timed.ref

(** Tags for rewriting configuration. *)
type rw_tag =
  [ `NoBeta (** If true, no beta-reduction is performed. *)
  | `NoRw (** If true, no user-defined rewrite rule is used. *)
  | `NoExpand (** If true, definitions are not expanded. *) ]

(** Functions that use the rewriting engine and accept an optional argument
    [tags] of type [rw_tag list] have the following behaviour.
    - If the argument is not given, then no tag is active and the rewrite
      engine is not constrained: it uses user defined reduction rules, it
      expands variable definitions (that are stored in the {!ctxt}) and
      performs beta reductions.
    - Each tag if present disables some functionality of the rewrite
      engine. The descriptions of the functionalities are given in the
      documentation of {!rw_tag}. *)

(** Reduction functions also accept an optional {!problem} that is used to
    store metavariables that may be created while rewriting. Such
    metavariables may be created by particular rewrite rules (such as
    unification rules), but not by rules declared with [rule t ↪ u;]. *)

(** {b NOTE} that all reduction functions, and {!eq_modulo}, may reduce
    in-place some subterms of the reduced term. *)

(** [whnf ?tags c t] computes a whnf of the term [t] in context
    [c]. *)
val whnf : ?tags:rw_tag list -> ctxt -> term -> term

(** [eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c]. *)
val eq_modulo : ctxt -> term -> term -> bool

(** [pure_eq_modulo c a b] tests the convertibility of [a] and [b] in context
   [c] with no side effects. *)
val pure_eq_modulo : ctxt -> term -> term -> bool

(** [snf ~dtree c t] computes a snf of [t], unfolding the variables defined in
    the context [c]. The function [dtree] maps symbols to dtrees. *)
val snf : ?dtree:(sym -> dtree) -> ?tags:rw_tag list -> ctxt -> term -> term

(** [hnf ?tags c t] computes a head-normal form of the term [t] in
    context [c]. *)
val hnf : ?tags:rw_tag list -> ctxt -> term -> term

(** [simplify t] computes a beta whnf of [t] belonging to the set S such that:
    - terms of S are in beta whnf normal format
    - if [t] is a product, then both its domain and codomain are in S. *)
val simplify : term -> term

(** If [s] is a non-opaque symbol having a definition, [unfold_sym s t]
   replaces in [t] all the occurrences of [s] by its definition. *)
val unfold_sym : sym -> term -> term

(** Dedukti evaluation strategies. *)
type strategy =
  | WHNF (** Reduce to weak head-normal form. *)
  | HNF  (** Reduce to head-normal form. *)
  | SNF  (** Reduce to strong normal form. *)
  | NONE (** Do nothing. *)

type strat =
  { strategy : strategy   (** Evaluation strategy. *)
  ; steps    : int option (** Max number of steps if given. *) }

(** [eval s c t] evaluates the term [t] in the context [c] according to
   strategy [s]. *)
val eval : strat -> ctxt -> term -> term
