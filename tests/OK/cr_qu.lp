// confluent system
constant symbol A:TYPE;
symbol ? : A → A → A; notation ? infix 10;
rule $x ? $x ↪ $x
with ($u ? _) ? (_ ? $y) ↪ $u ? $y
with $v ? (_ ? $y) ↪ $v ? $y
with ($u ? _) ? $y ↪ $u ? $y;
