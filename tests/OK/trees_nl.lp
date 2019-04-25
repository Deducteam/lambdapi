require open tests.OK.nat
require open tests.OK.bool

symbol eq_nl : N ⇒ N ⇒ B

rule eq_nl (s &x) (s &x) → true
 and eq_nl 0      0      → true
 and eq_nl (s _)  0      → false
 and eq_nl 0      (s _)  → false

assert eq_nl 3 3 : B