// Let syntax
symbol T : TYPE
symbol a : T

// Simple
type let x ≔ a in x

// Nested
type let x ≔ a in let y ≔ a in λ _, y
assert let x ≔ a in let y ≔ a in λ_, y ≡ λ_, a

// With arguments
type let f x ≔ x in f a
assert let f x ≔ x in f a ≡ a

// With type annotated arguments
type let f (x : T) ≔ λ _, x in f a
assert let f (x: T) ≔ λ_, x in f a ≡ λ_, a

// In rewrite rules
symbol f : T ⇒ T
rule f _ → let x ≔ a in x
assert f a ≡ a

// Should raise a warning (x not used in body)
assert f a ≡ let x ≔ a in a
