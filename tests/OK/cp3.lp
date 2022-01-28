// test local confluence of group theory

symbol G:TYPE;

symbol *:G → G → G; notation * infix 10;

// symbol 1:G;
symbol e:G;

//symbol ⁻¹:G → G; notation ⁻¹ postfix;
symbol inv:G → G;

rule ($x * $y) * $z ↪ $x * ($y * $z)

with $x * e ↪ $x
with e * $x ↪ $x

with inv $x * $x ↪ e
with $x * inv $x ↪ e

with inv $x * ($x * $y) ↪ $y
with $x * (inv $x * $y) ↪ $y

with inv e ↪ e
with inv (inv $x) ↪ $x
with inv ($x * $y) ↪ inv $y * inv $x;
