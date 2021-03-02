constant symbol Term : TYPE;
constant symbol Prop : TYPE;
symbol prf : Prop → TYPE;
symbol equals : Term → Term → Prop;
rule prf (equals $x $y) ↪ Π p, prf (p $x) → prf (p $y);
