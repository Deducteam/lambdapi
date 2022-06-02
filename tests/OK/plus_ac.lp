symbol N:TYPE;
symbol 0:N;
symbol s:N → N;
associative commutative symbol +:N → N → N;
notation + infix 10;
assert x y z ⊢ (x + s y) + s(s z) ≡ s(s z) + (x + s y);
compute λ x y z, (x + s y) + s(s z);
