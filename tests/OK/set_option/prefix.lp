constant symbol B : TYPE;

symbol ∧ : B → B → B;
symbol ∨ : B → B → B;
symbol ¬  : B → B;

set notation ∨ infix right 5;
set notation ∧ infix right 6;
set notation ¬ prefix 7;

assert ⊢ λ x y z t, x ∨ ¬ y ∧ z ∨ t ≡ λ x y z t, x ∨ (((¬ y) ∧ z) ∨ t);

assert ⊢ λ p, ¬ ¬ p ≡ λ p, ¬ (¬ p);

assert ⊢ λ p x, ¬ p x ≡ λ p x, ¬ (p x);
