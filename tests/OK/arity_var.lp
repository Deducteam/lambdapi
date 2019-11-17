// Test on variable arity
require open tests.OK.nat

symbol F : N ⇒ TYPE
rule F 0      → N
 and F (s &n) → N ⇒ F &n

symbol c : ∀ n, F n

constant symbol R : TYPE
constant symbol r : R
constant symbol s : R

symbol f : N ⇒ R
rule f (c 0)   → r
 and f (c 1 _) → s

assert f (c 0)   : R
assert f (c 1 2) : R
