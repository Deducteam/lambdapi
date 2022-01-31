// test computation of critical pairs

symbol A:TYPE;

constant symbol z:A;
constant symbol s:A → A;
symbol a:A → A → A;

rule a z $x ↪ $x
with a (s $x) $y ↪ s (a $x $y);
