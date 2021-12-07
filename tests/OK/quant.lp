constant symbol Set : TYPE;

injective symbol τ : Set → TYPE;

constant symbol prop : Set;

symbol Prop ≔ τ prop;

constant symbol ⊤ : Prop;

constant symbol ∀ [a] : (τ a → Prop) → Prop;

notation ∀ quantifier;

constant symbol ⇒ : Prop → Prop → Prop;

notation ⇒ infix right 5;

compute λ p q, ∀ (λ x, p x ⇒ q x);
// should print λ p, `∀ x, (p x ⇒ q x)

compute λ p, `∀ x, p x;
// should print λ p, `∀ x, p x

compute λ p q, (`∀ x, p x) ⇒ q;
// should print λp q, (`∀ x, p x) ⇒ q

flag "print_domains" on;
compute λ p, `∀ x, p x;
// should print λ p : τ ?8 → τ prop, `∀ x : τ ?8 → τ prop, p x

flag "print_domains" off;
flag "print_implicits" on;
compute λ p, `∀ x, p x;
// should print λ p, @∀ ?8 (λ x, p x)

flag "print_domains" on;
compute λ p, `∀ x, p x;
// should print λ p : τ ?8 → τ prop, @∀ ?8 (λ x:τ ?8, p x)
