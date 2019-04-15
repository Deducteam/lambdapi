require nat
open nat

symbol power : Nat ⇒ Nat ⇒ Nat
rule power _      0      → 1
 and power &x (S &y)     → mult &x (power &x &y)

symbol fact : Nat ⇒ Nat
rule fact 0      → 1
 and fact (S &x) → mult (S &x) (fact &x)

compute power 7 6
compute fact 8
