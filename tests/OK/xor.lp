symbol B:TYPE;

symbol 0:B;
associative commutative symbol +:B → B → B; notation + infix right 20;

rule 0 + $x ↪ $x
with $x + 0 ↪ $x
with $x + $x ↪ 0;

compute λ x, (x + 0) + (x + x + x);

assert x ⊢ x + 0 ≡ x + x + x;
