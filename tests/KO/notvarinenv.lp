// From issue #70

constant symbol Nat : TYPE;

constant symbol z : Nat;
constant symbol s : Nat → Nat;

symbol f : (Nat → Nat) → Nat;

rule f (λ x, $m[x,z]) ↪ z;
