// Let syntax
constant symbol T : TYPE
constant symbol a : T

// Simple
type let x ≔ a in x

// Nested
type let x ≔ a in let y ≔ a in λ _, y
assert let x ≔ a in let y ≔ a in λ_, y ≡ λ_, a

// With arguments
type let f x ≔ x in f a
assert let f x ≔ x in f a ≡ a

// With type annotated arguments
set flag "print_domains" on
type let f (x : T) ≔ λ _, x in f a
// assert let f (x: T) ≔ λ(_:T), x in f a ≡ λ(_:T), a
// TODO: need type annotation for bound variable of let

// In rewrite rules
symbol f : T ⇒ T
rule f _ → let x ≔ a in x
assert f a ≡ a
