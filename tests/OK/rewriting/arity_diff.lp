// Rules with different arities
require open tests.OK.nat;

symbol id : N → N;
rule id $x ↪ $x;

symbol add' : N → N → N;
rule add' 0 ↪ id                   // arity 1
with add' (s $x) $y ↪ $x + $y + 1; // arity 2

assert ⊢ add' 0 0 ≡ 0;

symbol g : N → N → N;
symbol f : (N → N → N) → (N → N) → N;
rule f g (g $x) ↪ $x;

assert ⊢ f g (g 0) ≡ 0;

