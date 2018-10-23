require open stdlib.logic
require open stdlib.bool

// Encoding of natural numbers
symbol const nat  : U

// Real natural numbers
symbol const N : TYPE

symbol const z : N
symbol const s : N ⇒ N

// Rewriting rule for the encoding of natural numbers
rule T nat → N

// Induction principle on N.
symbol nat_ind : ∀ (p:N⇒Prop), P(p z) ⇒ (∀n, P(p n) ⇒ P(p (s n))) ⇒ ∀n, P(p n)

rule nat_ind _  &u _  z      → &u
rule nat_ind &p &u &v (s &n) → &v &n (nat_ind &p &u &v &n)

// Enabling built-in natural number literal, and example
set builtin "0"  ≔ z
set builtin "+1" ≔ s

definition forty_two ≔ 42

// Addition function
symbol add : N ⇒ N ⇒ N

rule add z      &n     → &n
rule add (s &m) &n     → s (add &m &n)

// Multiplication function
symbol mul : N ⇒ N ⇒ N

rule mul z      _      → z
rule mul (s &m) &n     → add &n (mul &m &n)

// Doubling function
definition double n ≔ mul n 2

// Boolean equality function
symbol eq_nat : N ⇒ N ⇒ B

rule eq_nat z      z      → true
rule eq_nat (s &m) (s &n) → eq_nat &m &n
rule eq_nat z      (s _)  → false
rule eq_nat (s _)  z      → false

// Predicate "Lower or equal than"
symbol const le_nat : N ⇒ N ⇒ Prop
symbol le_n : ∀n, P(eq nat n n)
symbol le_S : ∀n m, P(le_nat n m) ⇒ P(le_nat n (s m))

// Function "Lower or equal than"
symbol le_nat_bool : N ⇒ N ⇒ B

rule le_nat_bool z      _      → true
rule le_nat_bool (s &m) z      → false
rule le_nat_bool (s &m) (s &n) → le_nat_bool &m &n

// Greater or equal than function
definition ge_nat_bool x y ≔ le_nat_bool y x

// Stricly lower than function
definition lt_nat_bool x y ≔ le_nat_bool (s x) y

// Stricly greater than function
definition gt_nat_bool x y ≔ lt_nat_bool y x

// Maximum
symbol max : N ⇒ N ⇒ N
rule max z &y          → &y
// in the following rule, it's more convenient to have the firts argument be &x instead of (s &x)
rule max &x z          → &x
rule max (s &x) (s &y) → s (max &x &y)

