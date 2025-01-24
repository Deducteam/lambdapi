symbol B:TYPE;

symbol O:B;
associative commutative symbol +:B → B → B; notation + infix right 20;

rule O + $x ↪ $x
with $x + O ↪ $x
with $x + $x ↪ O;

compute λ x, (x + O) + (x + x + x);

assert x ⊢ x + O ≡ x + x + x;
