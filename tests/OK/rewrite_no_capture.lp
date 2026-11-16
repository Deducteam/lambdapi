require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.Impred
  tests.OK.PropExt;

symbol p : τ (ι ⤳ o);
symbol q : τ o;

// A genuinely constant quantified body can be rewritten normally.
opaque symbol good_constant_rewrite :
  π ((∀ (λ (_ : τ ι), q)) = q) ≔
begin
  rewrite (∀_const ι q);
  reflexivity
end;

// The lemma's constant body must not be instantiated with p x, where x is
// bound inside the matched quantifier. Previously this escaped variable
// caused an assertion failure, which try does not catch.
opaque symbol reject_dependent_quantifier :
  π ((∀ (λ x, p x)) = (∀ (λ x, p x))) ≔
begin
  try rewrite ∀_const;
  reflexivity
end;
