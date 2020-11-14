require tests.OK.PrintA as A;
compute tests.OK.PrintA.f; // should print A.f
compute A.f; // should print A.f
assert ⊢ tests.OK.PrintA.f ≡ A.f;
