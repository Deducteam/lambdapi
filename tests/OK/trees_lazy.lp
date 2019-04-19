require open tests.OK.nat

symbol l : N ⇒ N ⇒ N
rule l &x      0     → l 0 &x
 and l 0       _     → 0
 and l (s &x) (s &y) → l &x &y

symbol fact : N ⇒ N
rule fact 0      → 1
 and fact (s &x) → (s &x) × (fact &x)

compute l 0 (s (fact 99))
// Second 's' is discovered by rule 2
compute l (s (s (fact 99))) 1

symbol chaina : N ⇒ N ⇒ N
symbol chainb : N ⇒ N ⇒ N
symbol chainc : N ⇒ N ⇒ N
rule chaina 0      &x → chainb &x &x
 and chainb (s &x) &y → chainc &x &y

compute chaina 0 (fact 6)
