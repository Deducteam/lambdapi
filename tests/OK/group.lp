// decision procedure for group theory
symbol G : TYPE;
symbol e : G;
symbol ⋅ : G → G → G;
notation ⋅ infix 10;
symbol inv : G → G;
rule ($x ⋅ $y) ⋅ $z ↪ $x ⋅ ($y ⋅ $z)
with e ⋅ $x ↪ $x
with $x ⋅ e ↪ $x
with inv $x ⋅ $x ↪ e
with $x ⋅ inv $x ↪ e
with inv $x ⋅ ($x ⋅ $y) ↪ $y
with $x ⋅ (inv $x ⋅ $y) ↪ $y
with inv e ↪ e
with inv (inv $x) ↪ $x
with inv ($x ⋅ $y) ↪ inv $y ⋅ inv $x;
