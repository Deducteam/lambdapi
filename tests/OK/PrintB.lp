require open tests.OK.PrintA;
//set verbose 3
compute tests.OK.PrintA.f a a; // should print a+a
compute a + a; // should print a+a
symbol B:TYPE;
symbol b:B;
symbol f:B → B → B;
compute a + a; // should print a+a
compute tests.OK.PrintA.f a a; // should print a+a
assert ⊢ tests.OK.PrintA.f a a ≡ a + a;
compute f b b; // should print f b b
set infix 5 "×" ≔ f;
compute a + a; // should print a+a
compute tests.OK.PrintA.f a a; // should print a+a
assert ⊢ tests.OK.PrintA.f a a ≡ a + a;
compute f b b; // should print b*b
assert ⊢ f b b ≡ b × b;
compute b × b; // should print b*b
symbol g:B → B → B;
set infix 5 "+" ≔ g;
compute b + b; // should print b+b
compute g b b; // should print b+b
assert ⊢ g b b ≡ b + b;
compute tests.OK.PrintA.f a a; // should print tests.OK.PrintA.f a a
