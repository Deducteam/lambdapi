constant symbol Set : TYPE;

injective symbol τ : Set → TYPE;

constant symbol prop : Set;

symbol Prop ≔ τ prop;

constant symbol ⊤ : Prop;

constant symbol ∀ {a} : (τ a → Prop) → Prop;

// set quantifier ∀;

constant symbol imp : Prop → Prop → Prop;

set infix right 5 "⇒" ≔ imp;

compute λ p q, ∀ (λ x, p x ⇒ q x); // should print λp,∀x,p x

compute λ p, `∀ x, p x; // should print λp,∀x,p x

compute λ p q, (`∀ x, p x) ⇒ q; // should print λp q, (∀x,p x) ⇒ q

set flag "print_implicits" on;

compute λ p, ∀ (λ x, p x); // should print λp,∀x:τ?,p x
