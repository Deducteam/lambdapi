constant symbol Nat : TYPE;
constant symbol zero : Nat;
constant symbol succ : Nat → Nat;
symbol double : Nat → Nat;
rule double zero ↪ zero
with double (succ $n) ↪ succ (succ (double $n));
