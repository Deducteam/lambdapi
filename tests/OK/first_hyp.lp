require open tests.OK.Tactic;

symbol Set: TYPE;
injective symbol τ: Set → TYPE;
injective symbol P [T]: τ T → Prop;

symbol test1 T (a b: τ T): π (P a) → π (P b) → π (P a) ≔
begin
  assume T a b h1 h2;
debug +t;
  eval #first_hyp (λ _ _ ph, #apply ph);
end;

symbol test2 T (a b: τ T): π (P a) → π (P b) → π (P a) ≔
begin
  assume T a b h1 h2;
  first_hyp (λ _ _ ph, #apply ph);
end;
