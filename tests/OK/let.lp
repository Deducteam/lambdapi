// Let syntax
constant symbol T : TYPE;
constant symbol a : T;

// Simple
type let x ≔ a in x;

// Nested
type let x ≔ a in let y ≔ a in λ _, y;
assert ⊢ let x ≔ a in let y ≔ a in λ _, y ≡ λ _, a;

// With arguments
type let f x ≔ x in f a;
assert ⊢ let f x ≔ x in f a ≡ a;

// In rewrite rules
symbol f : T → T;
rule f _ ↪ let x ≔ a in x;
assert ⊢ f a ≡ a;

// With type annotated arguments
flag "print_domains" on;
compute let x : T ≔ a in x;
// Type annotation on products
type let f x : T ≔ a in f;
type let f (x : T) ≔ λ _, x in f a;
assert ⊢ let f (x:T) : T → T ≔ λ(_:T), x in f a ≡ λ(_:T), a;
// dependent type let
symbol Dt : T → TYPE;
symbol dt x : Dt x;
type let f x : Dt x ≔ dt x in f;
