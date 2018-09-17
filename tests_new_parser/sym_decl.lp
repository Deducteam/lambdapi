// A type for the natural numbers.
symbol const Nat : TYPE

// Zero and successor symbols.
symbol const zero : Nat
symbol const succ : Nat ⇒ Nat
//symbol injective succ : Nat ⇒ Nat

// Addition and multiplication
symbol add : Nat ⇒ Nat ⇒ Nat
symbol mul : Nat ⇒ Nat ⇒ Nat
