require open tests.OK.nat

definition upper ≔ 3000

symbol loop : N ⇒ N ⇒ N
rule loop (s &x) 0      → loop &x upper
 and loop &x     (s &y) → loop &x &y

compute loop upper upper