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

constant symbol imp : Prop → Prop → Prop

set infix right 5 "⇒" ≔ imp

compute λp q, ∀ (λx,p x ⇒ q x) // should print λp,∀x,p x

compute λp, ∀x,p x // should print λp,∀x,p x

compute λp q, (∀x,p x) ⇒ q // should print λp q, (∀x,p x) ⇒ q

set flag "print_implicits" on

compute λp, ∀ (λx,p x) // should print λp,∀x:τ?,p x
