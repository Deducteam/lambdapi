symbol N:TYPE;
symbol O:N;
symbol s:N → N;
right associative commutative symbol +:N → N → N;
notation + infix 10;
assert x y z ⊢ (x + s y) + s(s z) ≡ s(s z) + (x + s y);
compute λ x y z, (x + s y) + s(s z);
