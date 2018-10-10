// From issue #70

symbol const Nat : TYPE

symbol const z : Nat
symbol const s : Nat ⇒ Nat

symbol f : (Nat ⇒ Nat) ⇒ Nat

rule f (λx, &m[x,z]) → z
