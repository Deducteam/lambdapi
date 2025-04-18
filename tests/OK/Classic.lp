// classical logic

require open tests.OK.Set tests.OK.Prop tests.OK.FOL;

symbol em p : π (p ∨ ¬ p); // excluded middle

opaque symbol ¬¬ₑ p : π (¬ ¬ p) → π p ≔
begin
assume p nnp; apply ∨ₑ (em p)
{ assume h; refine h }
{ assume np; apply ⊥ₑ; refine nnp np }
end;

opaque symbol ∨¬ᵢ p q : π (p ⇒ q) → π (¬ p ∨ q) ≔
begin
assume p q pq; apply ∨ₑ (em p)
{ assume hp; refine ∨ᵢ₂ _; refine pq hp }
{ assume np; refine ∨ᵢ₁ np }
end;

opaque symbol ∃¬ᵢ a p : π (¬ (∀ p)) → π (`∃ x : τ a, ¬ (p x)) ≔
begin
assume a p not_all_p; apply ∨ₑ (em (`∃ x, ¬ (p x)))
{ assume h; apply h }
{ assume not_ex_not_p; apply ⊥ₑ; apply not_all_p;
  have h: π (`∀ x, ¬ ¬ (p x))
    { refine ¬∃ (λ x, ¬ (p x)) _; refine not_ex_not_p};
  assume x; apply ¬¬ₑ; refine h x
}
end;
