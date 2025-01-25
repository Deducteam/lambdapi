symbol N:TYPE;

symbol O:N;
symbol s:N → N;

symbol G:TYPE;

symbol e:G;
symbol *:G → G → G; notation * infix 10;

rule $x * e ↪ $x
with e * $x ↪ $x;

symbol ⋅:N → G → G; notation ⋅ infix 20;

rule O ⋅ $x ↪ e
with s $n ⋅ $x ↪ $x * $n ⋅ $x;

compute λ x, O ⋅ x;
compute λ x, (s(s(s O))) ⋅ x;
