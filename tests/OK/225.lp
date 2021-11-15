symbol T:TYPE;
symbol a:T;
symbol f:(T → T) → T;
rule f (λ x, $F.[x]) ↪ a;
assert ⊢ λ (x:T), f(λ y, x) ≡ λ (x:T), a;
assert ⊢ f (λ x, x) ≡ a;
