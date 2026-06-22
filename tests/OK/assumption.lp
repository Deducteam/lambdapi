symbol Prop : TYPE;
symbol Set: TYPE;
injective symbol π: Prop → TYPE;
injective symbol τ: Set → TYPE;

symbol T: Set;
constant symbol P: τ T → Prop;

symbol test1 a b: π (P a) → π (P b) → π (P a) ≔
begin
  assume a b h1 h2;
  assumption
end;

symbol test2 a: (Π x, π (P x)) → π (P a) ≔
begin
  assume a h;
  iassumption;
end;
