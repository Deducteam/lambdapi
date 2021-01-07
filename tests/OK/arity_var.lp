// Test on variable arity
require open tests.OK.nat;

symbol F : N → TYPE;
rule F 0      ↪ N
with F (s $n) ↪ N → F $n;

symbol c : Π n, F n;

constant symbol R : TYPE;
constant symbol r : R;
constant symbol s : R;

symbol f : N → R;
rule f (c 0)   ↪ r
with f (c 1 _) ↪ s;

assert ⊢ f (c 0)   : R;
assert ⊢ f (c 1 2) : R;
