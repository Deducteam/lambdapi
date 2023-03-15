require tests.OK.boolean as B;
symbol T : (B.B → B.B) → TYPE;
symbol bool_neg: B.B → B.B;
symbol foo : T B.bool_neg;
symbol bar : T bool_neg;
assertnot ⊢ T B.bool_neg ≡ T bool_neg;
