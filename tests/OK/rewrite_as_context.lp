require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.FunExt
  tests.OK.Impred;

symbol a : τ ι;
symbol b : τ ι;
symbol f : τ (ι ⤳ ι);
symbol g : τ (ι ⤳ ι);
symbol q : τ (ι ⤳ ι ⤳ o);
symbol q_fun : τ ((ι ⤳ ι) ⤳ (ι ⤳ ι) ⤳ o);

symbol eq_point x : π (f x = g x);
symbol eq_lambda : π ((λ x, f x) = (λ x, g x)) ≔
  funExt (λ x, f x) (λ x, g x) eq_point;

symbol target_shape : π ((q a b) ∧ (q (g a) b));

// Skip the first context because its identifier does not match f _.
symbol test_shape : π ((q a b) ∧ (q (f a) b)) ≔
begin
  rewrite .[f _ as id in q id b] eq_point;
  refine target_shape
end;

symbol target_repeated :
  π ((q (f a) (f b)) ∧ (q (g b) (g b)));

// The combined pattern matches the first context, but its two identifier
// values disagree. Continue searching and rewrite the second context.
symbol test_repeated : π ((q (f a) (f b)) ∧ (q (f b) (f b))) ≔
begin
  rewrite .[f _ as id in q id id] eq_point;
  refine target_repeated
end;

symbol target_binders : π (q_fun (λ x, g x) (λ y, g y));

// Each copy of the selector pattern has its own binder-dependent hole.
// Repeated identifier values still agree modulo alpha equivalence.
symbol test_binders : π (q_fun (λ x, f x) (λ y, f y)) ≔
begin
  rewrite .[(λ z, f _) as id in q_fun id id] eq_lambda;
  refine target_binders
end;
