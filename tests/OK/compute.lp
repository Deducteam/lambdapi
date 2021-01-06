symbol N : TYPE;
symbol z : N;
symbol s : N → N;
symbol add : N → N → N;
rule add z $x ↪ $x
with add (s $x) $y ↪ add $x (s $y);
symbol one ≔ s z;
symbol two ≔ s one;
compute add two two;
