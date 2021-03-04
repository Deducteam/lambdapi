symbol A:TYPE;
symbol a:A;
symbol +:A → A → A;
set notation + infix 5;
//set verbose 3
compute a + a;
compute + a a; // should print a+a
assert ⊢ a + a ≡ + a a;
