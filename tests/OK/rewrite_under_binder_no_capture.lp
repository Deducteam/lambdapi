require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.FunExt
  tests.OK.Impred tests.OK.PropExt tests.OK.Tactic;

builtin "arr" ≔ ⤳;
builtin "funExt" ≔ funExt;

symbol p : τ (ι ⤳ o);

// Double-negation elimination under the quantifier requires lifting over x.
// The subsequent constant-quantifier rewrite must reject the dependent body
// p x: instantiating its constant parameter with p x would let x escape.
// Trying that rewrite must fail cleanly, leaving the goal available below.
opaque symbol test_rewrite_under_binder_no_capture :
  π ((∀ (λ x, ¬ ¬ p x)) ⇒ (∀ (λ x, p x))) ≔
begin
  rewrite ¬¬ₑ_eq;
  eval (#try (#rewrite "" "" [prop] ∀_const));
  // The rejected rewrite leaves an implication from a proposition to itself.
  simplify;
  assume h;
  refine h
end;
