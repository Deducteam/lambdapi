constant symbol Set : TYPE

set declared "τ"

injective symbol τ : Set → TYPE

constant symbol prop : Set

definition Prop ≔ τ prop

set declared "⊤"

constant symbol ⊤ : Prop

set declared "∀"

constant symbol ∀ {a} : (τ a → Prop) → Prop

set quantifier ∀

compute ∀ (λx,⊤) // should print ∀x,⊤

compute ∀x,⊤ // should print ∀x,⊤

set flag "print_implicits" on

compute ∀ (λx,⊤) // should print ∀x:?5,T
