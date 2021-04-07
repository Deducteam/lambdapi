// test commutative and associative-commutative symbols

constant symbol A : TYPE;

commutative symbol + : A → A → A;
notation + infix 10;
assert x y ⊢ x + y ≡ y + x;

associative commutative symbol * : A → A → A;
notation * infix 10;
debug +m;
assert x y ⊢ x * y ≡ y * x;
assert x y z ⊢ (x * y) * z ≡ x * (y * z);
assert x y z ⊢ (x * y) * z ≡ (z * x) * y;
