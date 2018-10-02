require open proofs.bool

// Data type of natural numbers.

symbol const N : TYPE

symbol const z : N
symbol const s : N ⇒ N

// Enabling built-in natural number literal, and example.

set builtin "0"  ≔ z
set builtin "+1" ≔ s

definition forty_two ≔ 42

// Addition function.

symbol add : N ⇒ N ⇒ N

rule add z      &n     → &n
rule add (s &m) &n     → s (add &m &n)
rule add &m     z      → &m
rule add &m     (s &n) → s (add &m &n)

// Multiplication function.

symbol mul : N ⇒ N ⇒ N

rule mul z      _      → z
rule mul (s &m) &n     → add &n (mul &m &n)
rule mul _      z      → z
rule mul &m     (s &n) → add &m (mul &m &n)

// Doubling function.

definition double n ≔ mul n 2

// Equality function.

symbol eq_nat : N ⇒ N ⇒ B

rule eq_nat z      z      → true
rule eq_nat (s &m) (s &n) → eq_nat &m &n
rule eq_nat z      (s _)  → false
rule eq_nat (s _)  z      → false

// Less than function.

symbol le_nat : N ⇒ N ⇒ B

rule le_nat z      z      → false
rule le_nat z      (s _)  → true
rule le_nat (s &m) (s &n) → le_nat &m &n
