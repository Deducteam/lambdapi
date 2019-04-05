require nat
open nat

symbol constant State : TYPE
symbol constant finished : State
symbol constant computing : State

definition upper ≔ 2000

symbol const loop : Nat ⇒ Nat ⇒ State
rule loop 0      0      → finished
 and loop (S &x) 0      → f &x upper
 and loop &x     (S &y) → f &x &y

compute f upper
assert (f upper) ≡ finished