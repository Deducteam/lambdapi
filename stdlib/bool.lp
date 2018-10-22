require open stdlib.logic

// Encoding of booleans
symbol const bool : U

// Real booleans
symbol const B : TYPE

symbol const true  : B
symbol const false : B

// Rewriting rule for the encoding of natural numbers
rule T bool       → B

// Induction principle on B (case analysis)
symbol bool_ind : ∀ (p:B⇒Prop), P(p true) ⇒ P(p false) ⇒ ∀b, P(p b)

rule bool_ind _ &t _  true  → &t
rule bool_ind _ _  &f false → &f

// Recursor on B
symbol bool_rect : ∀ (p:B⇒U), T(p true) ⇒ T(p false) ⇒ ∀b, T(p b)

rule bool_rect _ &t _  true  → &t
rule bool_rect _ _  &f false → &f

// Boolean negation by case analysis
definition bool_not b ≔ bool_rect (λ(x:B), bool) false true b // FIXME : infer predicate

// Boolean negation by rewrite rules
symbol bool_not_2 : B ⇒ B

rule bool_not_2 true  → false
rule bool_not_2 false → true

// Boolean disjunction by case analysis
definition bool_or b1 b2 ≔ (bool_rect (λ(x:B), bool) true b2) b1 // FIXME : infer predicate

// Boolean disjunction by rewrite rules
symbol bool_or_2 : B ⇒ B ⇒ B

rule bool_or_2 true  _     → true
rule bool_or_2 false &b2   → &b2
// the two additional rules are justified by bool_or_right_true and bool_or_right_false
rule bool_or_2 _     true  → true
rule bool_or_2 &b1   false → &b1

// Boolean conjunction by case analysis
definition bool_and b1 b2 ≔ (bool_rect (λ(x:B), bool) b2 false) b1 // FIXME : infer predicate

// Boolean conjunction by rewrite rules
symbol bool_and_2 : B ⇒ B ⇒ B

rule bool_and_2 true  &b2   → &b2
rule bool_and_2 false _     → false
// the two additional rules are justified by bool_and_right_true and bool_and_right_false
rule bool_and_2 &b1   true  → &b1
rule bool_and_2 _     false → false

// Boolean implication by case analysis
definition bool_impl a b ≔
  // here we gain by using the versions by rewriting
  bool_or_2 b (bool_not_2 a)

// Boolean implication by rewrite rules
symbol bool_impl_2 : B ⇒ B ⇒ B

rule bool_impl_2 true  &b2     → &b2
rule bool_impl_2 false _       → true
// the two additional rules are justified by bool_impl_right_true and bool_impl_right_false
rule bool_impl_2 _     true  → true
rule bool_impl_2 &b1   false → bool_not_2 &b1  

// Boolean exclusive or
definition bool_xor a b ≔
  let a_and_not_b = bool_and a (bool_not b) in
  let b_and_not_a = bool_and b (bool_not a) in
  bool_or a_and_not_b b_and_not_a

definition bool_xor_2 a b ≔
    bool_and (bool_or a b) (bool_not (bool_and a b))

