symbol N:TYPE;
symbol z:N;
symbol s:N → N;
builtin "0" ≔ z;
builtin "+1" ≔ s;
symbol +:N → N → N;
notation + infix 5;
rule 0 + $y ↪ $y
with s $x + $y ↪ s($x + $y);
compute 5 + 5;
assert ⊢ 5 + 5 ≡ 10;
