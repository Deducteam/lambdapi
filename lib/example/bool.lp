// Data type of booleans.

constant symbol B : TYPE

constant symbol true  : B
constant symbol false : B

// Declaration of the main boolean functions, with their notation.

symbol bool_neg : B ⇒ B
symbol bool_and : B ⇒ B ⇒ B
symbol bool_or  : B ⇒ B ⇒ B

set infix right 18 "∧" ≔ bool_and
set infix right 16 "∨" ≔ bool_and
set prefix      20 "¬" ≔ bool_neg

// Definition of negation.

rule ¬ true  → false
rule ¬ false → true
rule ¬ ¬ &a  → &a

// Definition of conjunction

rule true  ∧ &b    → &b
 and &b    ∧ true  → &b
 and false ∧ _     → false
 and _     ∧ false → false

// Definition of disjunction.

rule true  ∨ _     → true
 and _     ∨ true  → true
 and false ∨ &b    → &b
 and &b    ∨ false → &b

// Conditional.

symbol bool_if : B ⇒ B ⇒ B ⇒ B

rule bool_if true  &x _  → &x
rule bool_if false _  &x → &x

// More (defined) boolean functions.

definition bool_impl a b ≔ b ∨ ¬ a
definition bool_xor  a b ≔ (a ∨ b) ∧ ¬ (a ∧ b)

set infix right 14 "⇨" ≔ bool_impl
set infix right 16 "⊕" ≔ bool_xor

// Some tests.

assert (x y z : B) ⊢ x ∨ y ∨ ¬ z ≡ x ∨ (y ∨ ¬ z)
assert (x y z : B) ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z)
assert (x y z : B) ⊢ z ⇨ x ∨ y ∧ z ≡ z ⇨ (x ∨ (y ∧ z))
