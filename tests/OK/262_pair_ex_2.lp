require open tests.OK.{|262_pair_ex_1|}

symbol a : A
symbol b : A

definition P ≔ pair a a
definition Q ≔ pair a b

// Since pair reduces to _pair which forgets its second argument,
// P and Q are equal
assert P ≡ Q
