symbol Prop:TYPE;
symbol -:Prop → Prop; notation - prefix 10;
associative commutative symbol +: Prop → Prop → Prop; notation + infix right 5;
injective symbol π:Prop → TYPE;
symbol resolution x a b : π (x + a) → π (- x + b) → π (a + b);
opaque symbol test a b c d e :
  π (e + a + b) → π (c + d + - e) → π (a + b + c + d) ≔
begin
  assume a b c d e h1 h2;
  apply resolution e (b + a) (d + c) h1 h2
end;
