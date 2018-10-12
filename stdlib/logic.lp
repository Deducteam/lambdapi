// Type of data type

symbol const U : TYPE

// Interpretation of data types as types

symbol T : U ⇒ TYPE

// Encoding of the dependent product

symbol const pi : ∀ (a : U), (T a ⇒ U) ⇒ U

// Rewriting rule for the encoding of the dependent product

rule T (pi &a &f) → ∀ (x : T &a), T (&f x)



// Type of propositions

symbol const Prop : TYPE

// Interpretation of propositions as types

symbol P : Prop ⇒ TYPE

// Encoding of the universal quantification

symbol const all : ∀ (a : U), (T a ⇒ Prop) ⇒ Prop

// Rewriting rule for the encoding of the universal quantification

rule P (all &a &f) → ∀ (x : T &a), P (&f x)



// Leibniz equality.

symbol const eq : ∀a, T a ⇒ T a ⇒ Prop

symbol const refl  : ∀a x, P (eq a x x)
symbol const eqind : ∀a x y, P (eq a x y) ⇒ ∀ (p:T a⇒Prop), P (p y) ⇒ P (p x)

set builtin "P"     ≔ P
set builtin "T"     ≔ T
set builtin "eq"    ≔ eq
set builtin "eqind" ≔ eqind
set builtin "refl"  ≔ refl
