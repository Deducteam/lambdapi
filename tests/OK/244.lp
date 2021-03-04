// Precedence for prefix operators
symbol o : TYPE;
symbol ~ : o → o;
notation ~ prefix 5;
type λ p x, ~(p x);
type λ p x, ~ p x;
assert ⊢ λ p x,~(p x) ≡ λ p x,~ p x;
