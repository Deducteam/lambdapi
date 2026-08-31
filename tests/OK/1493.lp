require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.FunExt
  tests.OK.Impred tests.OK.Tactic;

symbol eps : τ ((ι ⤳ o) ⤳ ι);
symbol if : τ (o ⤳ ι ⤳ ι ⤳ ι);
symbol a : τ ι;
symbol b : τ ι;

symbol if_def :
  π (if =
     (λ (p : τ o), λ (x : τ ι), λ (y : τ ι),
        eps (λ (z : τ ι), (p ∧ z = x) ∨ (¬ p ∧ z = y))));

opaque symbol direct_eval_rewrite_ok :
  π ((¬ (if ⊤ a b = a)) ⇒
     (¬ (eps (λ (z : τ ι), (⊤ ∧ z = a) ∨ (¬ ⊤ ∧ z = b)) = a))) ≔
begin
  eval (#rewrite "" "" if_def);
  assume h;
  refine h
end;

opaque symbol parser_repeat_rewrite_ok :
  π ((¬ (if ⊤ a b = a)) ⇒
     (¬ (eps (λ (z : τ ι), (⊤ ∧ z = a) ∨ (¬ ⊤ ∧ z = b)) = a))) ≔
begin
  repeat rewrite if_def;
  assume h;
  refine h
end;

opaque symbol repro :

  π ((¬ (if ⊤ a b = a)) ⇒
     (¬ (eps (λ (z : τ ι), (⊤ ∧ z = a) ∨ (¬ ⊤ ∧ z = b)) = a))) ≔
begin
  eval (#repeat (#rewrite "" "" if_def));
  assume h;
  refine h
end;
