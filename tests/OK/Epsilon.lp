// Hilbert choice operator

require open tests.OK.FOL;

symbol ε [a:Set] : (τ a → Prop) → τ a;
symbol εᵢ [a:Set] (p:τ a → Prop) : π (∃ p) → π (p (ε p));

opaque symbol εₑ [a:Set] (p:τ a → Prop) : π (p (ε p)) → π (`∃ x, p x) ≔
begin
  assume a p h; refine ∃ᵢ (ε p) h
end;
