require nat
open nat
// Multiple recursions
symbol fib : Nat ⇒ Nat
rule fib 0                  → 0
 and fib 1                  → 1
 and fib (S (S &x)) → plus (fib (S &x)) (fib &x)

symbol fib3 : Nat ⇒ Nat
rule fib3 0 → 0
 and fib3 1 → 1
 and fib3 2 → 1
 and fib3 (plus 3 &x) → plus (fib3 (S (S &x)))
                             (plus (fib3 (S &x))
                                   (fib3 &x))

compute fib 27
compute fib3 22