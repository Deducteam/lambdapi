require open tests.OK.queries.PrintA;
//set verbose 3
compute tests.OK.queries.PrintA.+ a a; // should print a+a
compute a + a; // should print a+a
symbol B:TYPE;
symbol b:B;
symbol ×:B → B → B;
compute a + a; // should print a+a
compute tests.OK.queries.PrintA.+ a a; // should print a+a
assert ⊢ tests.OK.queries.PrintA.+ a a ≡ a + a;
compute × b b; // should print f b b
set notation × infix 5;
compute a + a; // should print a+a
compute tests.OK.queries.PrintA.+ a a; // should print a+a
assert ⊢ tests.OK.queries.PrintA.+ a a ≡ a + a;
compute × b b; // should print b*b
assert ⊢ × b b ≡ b × b;
compute b × b; // should print b*b
symbol +:B → B → B;
set notation + infix 5;
compute b + b; // should print b+b
compute + b b; // should print b+b
assert ⊢ + b b ≡ b + b;
compute tests.OK.queries.PrintA.+ a a; // should print tests.OK.queries.PrintA.+ a a
