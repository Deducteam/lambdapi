require nat
open nat

symbol l : Nat ⇒ Nat ⇒ Nat
rule l &x      0     → l 0 &x
 and l 0       _     → 0
 and l (S &x) (S &y) → l &x &y

symbol fact : Nat ⇒ Nat
rule fact 0      → 1
 and fact (S &x) → mult (S &x) (fact &x)

compute l 0 (S (fact 99))
// Second 'S' is discovered by rule 2
compute l (S (S (fact 99))) 1