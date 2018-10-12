require open stdlib.logic

// Encoding of booleans

symbol const bool : U

// Real booleans

symbol const B : TYPE

symbol const true  : B
symbol const false : B

// Rewriting rule for the encoding of natural numbers

rule T bool       → B

// Induction principle on B.

symbol bool_ind : ∀ (p:B⇒Prop), P(p true) ⇒ P(p false) ⇒ ∀b, P(p b)

rule bool_ind _ &t _  true  → &t
rule bool_ind _ _  &f false → &f

// Boolean negation.

symbol bool_not : B ⇒ B

rule bool_not true  → false
rule bool_not false → true

// Boolean disjunction.

symbol bool_or : B ⇒ B ⇒ B

rule bool_or true  _     → true
rule bool_or false &b    → &b
rule bool_or _     true  → true
rule bool_or &b    false → &b

// Boolean conjunction.

symbol bool_and : B ⇒ B ⇒ B

rule bool_and true  &b    → &b
rule bool_and false _     → false
rule bool_and &b    true  → &b
rule bool_and _     false → false

// Boolean implication

definition bool_impl a b ≔
  bool_or b (bool_not a)

// Boolean exclusive or

definition bool_xor  a b ≔
  let a_and_not_b = bool_and a (bool_not b) in
  let b_and_not_a = bool_and b (bool_not a) in
  bool_or a_and_not_b b_and_not_a

definition bool_xor_2 a b ≔
    bool_and (bool_or a b) (bool_not (bool_and a b))

