symbol N : TYPE;
symbol z : N;
symbol s : N → N;

symbol + : N → N → N;
set notation + infix left 5;
assert ⊢ z + z + z ≡ (z + z) + z;
assert ⊢ z + s z ≡ z + (s z);
assertnot ⊢ z + z + z ≡ z + (z + z);

symbol × : N → N → N;
set notation × infix right 6;
assertnot ⊢ z × z × z ≡ (z × z) × z;
assert ⊢ z × z × z ≡ z × (z × z);
