require open proofs.bool
require open proofs.nat

// Type of data type.

symbol const U : TYPE

// Interpretation function (for data types as types).

symbol injective T : U ⇒ TYPE

// Examples of data types and their interpretations.

symbol const bool : U
symbol const nat  : U
symbol const pi   : ∀ (a : U), (T a ⇒ U) ⇒ U

rule T bool       → B
rule T nat        → N
rule T (pi &a &f) → ∀ (x : T &a), T (&f x)

// Type of propositions and their interpretation as types.

symbol const Prop : TYPE

symbol const all : ∀ (a : U), (T a ⇒ Prop) ⇒ Prop

// Interpretation function (for propositions as types).

symbol injective P : Prop ⇒ TYPE

rule P (all &a &f) → ∀ (x : T &a), P (&f x)

// Induction principle on B.

symbol bool_ind : ∀ (p:B⇒Prop), P(p true) ⇒ P(p false) ⇒ ∀b, P(p b)

rule bool_ind _ &t _  true  → &t
rule bool_ind _ _  &f false → &f

// Induction principle on N.

symbol nat_ind : ∀ (p:N⇒Prop), P(p z) ⇒ (∀n, P(p n) ⇒ P(p (s n))) ⇒ ∀n, P(p n)

rule nat_ind _  &u _  z      → &u
rule nat_ind &p &u &v (s &n) → &v &n (nat_ind &p &u &v &n)

// Leibniz equality.

symbol const eq : ∀a, T a ⇒ T a ⇒ Prop

symbol const refl  : ∀a x, P (eq a x x)
symbol const eqind : ∀a x y, P (eq a x y) ⇒ ∀ (p:T a⇒Prop), P (p y) ⇒ P (p x)

set builtin "P"     ≔ P
set builtin "T"     ≔ T
set builtin "eq"    ≔ eq
set builtin "eqind" ≔ eqind
set builtin "refl"  ≔ refl