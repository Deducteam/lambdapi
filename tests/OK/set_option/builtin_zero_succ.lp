symbol N:TYPE;
symbol z:N;
symbol s:N → N;
set builtin "0" ≔ z;
set builtin "+1" ≔ s;
symbol add:N → N → N;
set infix 5 "+" ≔ add;
rule 0 + $y ↪ $y
with s $x + $y ↪ s($x + $y);
compute 5 + 5;
assert ⊢ 5 + 5 ≡ 10;
