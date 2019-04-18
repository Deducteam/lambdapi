require nat
open nat

definition upper ≔ 2000

symbol loop : Nat ⇒ Nat ⇒ Nat
rule loop (S &x) 0      → loop &x upper
 and loop &x     (S &y) → loop &x &y

compute loop upper upper