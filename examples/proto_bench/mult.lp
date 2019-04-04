symbol const Nat : TYPE
symbol const Z : Nat
symbol const S : Nat ⇒ Nat

set builtin "0" ≔ Z
set builtin "+1" ≔ S

symbol plus : Nat ⇒ Nat ⇒ Nat
rule plus 0      &x → &x
 and plus (S &x) &y → plus &x (S &y)

symbol mult : Nat ⇒ Nat ⇒ Nat
rule mult 0 _       → 0
 and mult (S &x) &y → plus &y (mult &x &y)

symbol power : Nat ⇒ Nat ⇒ Nat
rule power _      0      → 1
 and power &x (S &y)     → mult &x (power &x &y)

symbol fact : Nat ⇒ Nat
rule fact 0      → 1
 and fact (S &x) → mult (S &x) (fact &x)

compute power 7 6
compute fact 8