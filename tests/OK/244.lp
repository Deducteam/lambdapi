// Precedence for prefix operators
symbol o : TYPE;
symbol not : o → o;
set prefix 5 "~" ≔ not;
type λ p x, ~(p x);
type λ p x, ~ p x;
assert ⊢ λ p x,~(p x) ≡ λ p x,~ p x;
