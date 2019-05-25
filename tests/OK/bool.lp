// Data type of booleans.

symbol const B : TYPE

symbol const true  : B
symbol const false : B

// Boolean negation.

symbol bool_neg : B ⇒ B

rule bool_neg true  → false
 and bool_neg false → true

// Boolean disjunction.

symbol bool_or : B ⇒ B ⇒ B

rule bool_or true  _     → true
 and bool_or false &b    → &b
 and bool_or _     true  → true
 and bool_or &b    false → &b

// Boolean conjunction.

symbol bool_and : B ⇒ B ⇒ B

rule bool_and true  &b    → &b
 and bool_and false _     → false
 and bool_and &b    true  → &b
 and bool_and _     false → false

// More connectives.

definition bool_impl a b ≔
  bool_or b (bool_neg a)

definition bool_xor  a b ≔
  let a_and_not_b = bool_and a (bool_neg b) in
  let b_and_not_a = bool_and b (bool_neg a) in
  bool_or a_and_not_b b_and_not_a
