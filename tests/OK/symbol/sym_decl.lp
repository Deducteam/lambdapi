// A type for the natural numbers.
constant symbol Nat : TYPE;

// Zero and successor symbols.
constant symbol zero : Nat;
constant symbol succ : Nat → Nat;
//injective symbol succ : Nat → Nat

// Addition and multiplication
symbol add : Nat → Nat → Nat;
symbol mul : Nat → Nat → Nat;
