require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.Impred;

symbol b : τ ι;

symbol f : τ (ι ⤳ ι);
symbol g : τ (ι ⤳ ι);
symbol q : τ (ι ⤳ ι ⤳ o);

// Deliberately declare the symbol without registering the funExt builtin.
symbol funExt [a b] (f g : τ (a ⤳ b)) : (Π x, π(f x = g x)) → π(f = g);

symbol eq_point x : π (f x = g x);

symbol target_one_binder :
  π ((∀ (λ x, q (g x) b)) = ⊤);

// The redex depends on x, so rewriting requires equality lifting and must
// fail because the funExt builtin is missing. A symbol with that name alone
// is insufficient; otherwise the continuation would complete the proof.
symbol test_rewrite_under_one_binder :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite eq_point;
  refine target_one_binder
end;
