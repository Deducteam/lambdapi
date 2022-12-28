// decision procedure for group theory
symbol G : TYPE;
symbol 1 : G;
symbol ⋅ : G → G → G;
notation ⋅ infix 10;
symbol inv : G → G;
rule ($x ⋅ $y) ⋅ $z ↪ $x ⋅ ($y ⋅ $z)
with 1 ⋅ $x ↪ $x
with $x ⋅ 1 ↪ $x
with inv $x ⋅ $x ↪ 1
with $x ⋅ inv $x ↪ 1
with inv $x ⋅ ($x ⋅ $y) ↪ $y
with $x ⋅ (inv $x ⋅ $y) ↪ $y
with inv 1 ↪ 1
with inv (inv $x) ↪ $x
with inv ($x ⋅ $y) ↪ inv $y ⋅ inv $x;
