constant symbol B : TYPE;

symbol conj : B → B → B;
symbol disj : B → B → B;
symbol neg  : B → B;

set infix right 5 "∨" ≔ disj;
set infix right 6 "∧" ≔ conj;

set prefix 7 "¬" ≔ neg;

assert ⊢ λ x y z t, x ∨ ¬ y ∧ z ∨ t ≡ λ x y z t, x ∨ (((¬ y) ∧ z) ∨ t);

assert ⊢ λ p, ¬ ¬ p ≡ λ p, ¬ (¬ p);

assert ⊢ λ p x, ¬ p x ≡ λ p x, ¬ (p x);
