symbol N:TYPE;

symbol 0:N; builtin "0" ≔ 0;
symbol s:N → N; builtin "+1" ≔ s;

compute 0;
compute 3;

symbol G:TYPE;

symbol e:G;
symbol *:G → G → G; notation * infix 10;

rule $x * e ↪ $x
with e * $x ↪ $x;

symbol ⋅:N → G → G; notation ⋅ infix 20;

rule 0 ⋅ $x ↪ e
with s $n ⋅ $x ↪ $x * $n ⋅ $x;

compute λ x, 0 ⋅ x;
compute λ x, 3 ⋅ x;
