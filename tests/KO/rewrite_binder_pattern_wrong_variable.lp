require open tests.OK.rewrite_under_binders;

symbol target_closed : π ((∀ (λ x : τ ι, q (g b) b)) = ⊤);

// The selector requires f applied to its lambda-bound variable, but the
// goal contains f b, which is independent of that variable. Matching must
// reject this difference.
symbol test_rewrite_binder_pattern_wrong_variable :
  π ((∀ (λ x : τ ι, q (f b) b)) = ⊤) ≔
begin
  rewrite .[in (λ y, q (f y) b)] eq_point;
  refine target_closed
end;
