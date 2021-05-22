// A simple test on abstractions, taken from the [miller] tests.
symbol R : TYPE;

symbol flip : (R → R → R) → (R → R → R);
debug +iu;
flag "print_meta_types" on;
rule flip (λ x, λ y, $f[x; y]) ↪ λ (x:R), λ (y:R), $f[y; x];

symbol f : R → R → R;
symbol x : R;
symbol y : R;

compute flip (λ x, λ y, f x y);
assert ⊢ flip (λ x, λ y, f x y) ≡ λ x, λ y, f y x;
