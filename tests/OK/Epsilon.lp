require open tests.OK.FOL;

symbol ε [a:Set] : (τ a → Prop) → τ a;
symbol εᵢ [a:Set] (p:τ a → Prop) : π (∃ p) → π (p (ε p));
