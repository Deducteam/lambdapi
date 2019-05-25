require open tests.OK.nat

symbol power : N ⇒ N ⇒ N
rule power _      0  → 1
 and power &x (s &y) → &x × (power &x &y)

symbol fact : N ⇒ N
rule fact 0      → 1
 and fact (s &x) → (s &x) × (fact &x)

compute power 5 5
compute fact 7
