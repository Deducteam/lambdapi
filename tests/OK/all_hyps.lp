require open tests.OK.Tactic tests.OK.Eq;

symbol test1 T (a b c: τ T): π (a = c) → π (b = c) → π (a = b) ≔
begin
  assume T a b c h1 h2;
  eval (#all_hyps (λ _ _ ph, #rewrite "" "" ph));
  reflexivity;
end;

symbol test2 T (a b c: τ T): π (a = c) → π (b = c) → π (a = b) ≔
begin
  assume T a b c h1 h2;
debug +tu;
  all_hyps (λ l (h: U l) ph, @#rewrite "" "" l h ph);
  reflexivity
end;
