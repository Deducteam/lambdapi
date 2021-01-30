require open tests.OK.{|262_pair_ex_1|};

symbol a : A;
symbol b : A;

symbol P ≔ pair a a;
symbol Q ≔ pair a b;

// Since pair reduces to _pair which forgets its second argument,
// P and Q are equal
assert ⊢ P ≡ Q;
