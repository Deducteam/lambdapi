symbol const Nat : TYPE
symbol const Z : Nat
symbol const S : Nat ⇒ Nat

set builtin "0" ≔ Z
set builtin "+1" ≔ S

symbol plus : Nat ⇒ Nat ⇒ Nat
rule plus 0      &x → &x
 and plus (S &x) &y → plus &x (S &y)
