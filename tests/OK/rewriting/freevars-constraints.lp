// Check correctness regarding free variables constraints
symbol R : TYPE;
symbol zr : R;

symbol d : (R → R) → (R → R);

symbol ch : R → R;
symbol dx : (R → R → R) → (R → R → R);
rule dx (λ x y, $F[x]) ↪ λ (x y:R) , d (λ (x':R), $F[x']) x
with dx (λ x y, $F[y]) ↪ λ (x y:R) , zr;

assert ⊢ dx (λ x y, ch x) ≡ (λ (x' y:R) , d (λ x, ch x) x');
assert ⊢ dx (λ x y, ch y) ≡ λ (x y:R) , zr;

