constant symbol Nat: TYPE;
constant symbol Float: TYPE;
constant symbol round (_: Float): Nat;
coerce #c Float $t Nat ↪ round $t ;
constant symbol succ (_: Nat): Nat;
assert ⊢ λ x: Float, succ x ≡ λ x: Float, succ (round x);  
