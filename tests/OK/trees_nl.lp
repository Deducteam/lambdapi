require open tests.OK.nat
require open tests.OK.bool

symbol eq_nl : N ⇒ N ⇒ B

rule eq_nl (s &x) (s &x) → true
 and eq_nl 0      0      → true
 and eq_nl (s _)  0      → false
 and eq_nl 0      (s _)  → false

assert eq_nl 3 3 ≡ true

symbol f : N ⇒ N ⇒ N ⇒ B
rule f &x &x _  → true
 and f _  &x &x → false
compute f 4 4 11
compute f 4 11 11

symbol g : N ⇒ N ⇒ B
rule g &x &x → true

compute g 1 1