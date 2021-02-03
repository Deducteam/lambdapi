require tests.OK.queries.PrintA as A;
compute tests.OK.queries.PrintA.f; // should print A.f
compute A.f; // should print A.f
assert ⊢ tests.OK.queries.PrintA.f ≡ A.f;
