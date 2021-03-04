require tests.OK.queries.PrintA as A;
compute tests.OK.queries.PrintA.+; // should print A.+
compute A.+; // should print A.+
assert ⊢ tests.OK.queries.PrintA.+ ≡ A.+;
