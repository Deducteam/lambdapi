require open tests.OK.Prop tests.OK.Set tests.OK.Univ tests.OK.Tactic;

injective symbol P [T]: τ T → Prop;

symbol test1 T (a b: τ T): π (P a) → π (P b) → π (P a) ≔
begin
  assume T a b h1 h2;
  eval (#first_hyp (λ l (v: U l) ph, #apply ph));
end;

symbol test2 T (a b: τ T): π (P a) → π (P b) → π (P a) ≔
begin
  assume T a b h1 h2;
debug +t;
  first_hyp (λ l (v: U l) (ph: η v), #apply ph);
end;
