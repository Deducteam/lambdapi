require open tests.OK.prv_reduction_1

symbol a : A
symbol b : A

definition P ≔ pair a a
definition Q ≔ pair a b

assert P ≡ Q
