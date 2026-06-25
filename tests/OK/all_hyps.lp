require open tests.OK.Tactic;
require open tests.OK.Eq;

symbol test1 T (a b c: τ T): π (a = c) → π (b = c) → π (a = b) ≔
begin
  assume T a b c h1 h2;
  eval (#all_hyps (λ (h: Prop) (ph: π h),  #rewrite "" "" ph));
  reflexivity;
end;

symbol test2 T (a b c: τ T): π (a = c) → π (b = c) → π (a = b) ≔
begin
  assume T a b c h1 h2;
  all_hyps (λ h ph, #rewrite "" "" ph);
  reflexivity
end;
