symbol A:TYPE;
symbol a:A;
symbol f:A → A → A;
set infix 5 "+" ≔ f;
//set verbose 3
compute a + a;
compute f a a; // should print a+a
assert ⊢ a + a ≡ f a a;
