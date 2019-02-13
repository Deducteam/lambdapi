symbol N : TYPE
symbol z : N

symbol add : N⇒N⇒N
set infix left 5 "+" ≔ add
assert z+z+z ≡ (z+z)+z
assertnot z+z+z ≡ z+(z+z)

symbol mul : N⇒N⇒N
set infix right 6 "*" ≔ mul
assertnot z*z*z ≡ (z*z)*z
assert z*z*z ≡ z*(z*z)
