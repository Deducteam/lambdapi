constant symbol Term : TYPE;
constant symbol Prop : TYPE;
symbol prf : Prop → TYPE;
symbol equals : Term → Term → Prop;

//set flag "print_implicits" on
//set debug +siu

rule prf (equals $x $y) ↪ Π P, prf (P $x) → prf (P $y);
