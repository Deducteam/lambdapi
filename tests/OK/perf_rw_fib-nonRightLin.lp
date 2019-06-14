require open tests.OK.nat
// Multiple recursions
symbol fib : N ⇒ N
rule fib 0          → 0
 and fib 1          → 1
 and fib (&x + 2) → (fib (s &x)) + (fib &x)

symbol fib3 : N ⇒ N
rule fib3 0 → 0
 and fib3 1 → 1
 and fib3 2 → 1
 and fib3 (&x + 3) → (fib3 (&x + 2)) + (fib3 (&x + 1)) + (fib3 &x)

compute fib 27
compute fib3 22
