constant symbol B : TYPE;

symbol ∧ : B → B → B;
symbol ∨ : B → B → B;
symbol ¬  : B → B;

notation ∨ infix right 5;
notation ∧ infix right 6;
notation ¬ prefix 7;

assert ⊢ λ x y z t, x ∨ ¬ y ∧ z ∨ t ≡ λ x y z t, x ∨ (((¬ y) ∧ z) ∨ t);

assert ⊢ λ p, ¬ ¬ p ≡ λ p, ¬ (¬ p);

assert ⊢ λ p x, ¬ p x ≡ λ p x, ¬ (p x);

// Types and arrow

symbol o : B → TYPE;
notation o prefix 6;
assert (n : B) ⊢ o n → B ≡ (o n) → B;
