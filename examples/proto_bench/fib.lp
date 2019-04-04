// Multiple recursions
symbol const Nat : TYPE
symbol const Z : Nat
symbol const S : Nat ⇒ Nat

set builtin "0" ≔ Z
set builtin "+1" ≔ S

symbol plus : Nat ⇒ Nat ⇒ Nat
rule plus 0      &x → &x
 and plus (S &x) &y → plus &x (S &y)

symbol fib : Nat ⇒ Nat
rule fib 0          → 0
 and fib 1          → 1
 and fib (S (S &x)) → plus (fib (S &x)) (fib &x)

symbol fib3 : Nat ⇒ Nat
rule fib3 0 → 0
 and fib3 1 → 1
 and fib3 2 → 1
 and fib3 (plus 3 &x) → plus (fib3 (S (S &x))) (plus (fib3 (S &x)) (fib3 &x))

compute fib 27
compute fib3 22