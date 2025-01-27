require open tests.OK.natural;
// Multiple recursions
symbol fib : N → N;
rule fib z          ↪ 0
with fib (s z)      ↪ 1
with fib (s (s $x)) ↪ (fib (s $x)) + (fib $x);

symbol fib3 : N → N;
rule fib3 0              ↪ 0
with fib3 (s z)          ↪ 1
with fib3 (s (s z))      ↪ 1
with fib3 (s (s (s $x))) ↪ (fib3 ($x + 2)) + (fib3 ($x + 1)) + (fib3 $x);

assert ⊢ fib 15 ≡ 610;
compute fib 24; // ≡ 46368;
//compute fib3 21;
