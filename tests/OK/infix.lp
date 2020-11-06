symbol N : TYPE;
symbol z : N;
symbol s : N → N;

symbol add : N → N → N;
set infix left 5 "a" ≔ add;
assert z a z a z ≡ (z a z) a z;
assert z a s z ≡ z a (s z);
assertnot z a z a z ≡ z a (z a z);

symbol mul : N→N→N;
set infix right 6 "m" ≔ mul;
assertnot z m z m z ≡ (z m z) m z;
assert z m z m z ≡ z m (z m z);
