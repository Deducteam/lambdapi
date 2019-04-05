require nat
open nat

symbol const State : TYPE
symbol const finished : State
symbol const computing : State

definition upper ≔ 2000

symbol loop : Nat ⇒ Nat ⇒ State
rule loop 0      0      → finished
 and loop (S &x) 0      → loop &x upper
 and loop &x     (S &y) → loop &x &y

compute loop upper
assert (loop upper) ≡ finished