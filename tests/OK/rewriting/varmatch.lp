constant symbol A : TYPE;

constant symbol id : A → A;
symbol f : (A → A) → (A → A);
rule f (λ x, x) ↪ id;

assert ⊢ f (λ x, x) ≡ id;
