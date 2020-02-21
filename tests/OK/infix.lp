symbol N : TYPE
symbol z : N
symbol s : N ⇒ N

symbol add : N⇒N⇒N
symbol sub : N⇒N⇒N
symbol opp : N⇒N
set infix left 5 "+" ≔ add
set infix left 5 "-" ≔ sub
set prefix 7 "-" ≔ opp
assert z+z+z ≡ (z+z)+z
assert z + s z ≡ z + (s z)
assertnot z+z+z ≡ z+(z+z)
assert z + z - z ≡ (z + z) - z
assert z - z - z ≡ (z - z) - z
assert z - z + z ≡ (z - z) + z
assert -z + -z  ≡ opp z + opp z

symbol mul : N⇒N⇒N
set infix right 6 "*" ≔ mul
assertnot z*z*z ≡ (z*z)*z
assert z*z*z ≡ z*(z*z)
assert -z*-z ≡ opp z* opp z