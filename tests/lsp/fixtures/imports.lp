require open Stdlib.Nat;

symbol double : ℕ → ℕ;
rule double 0 ↪ 0
with double (+1 $n) ↪ +1 (+1 (double $n));
