require open tests.OK.FOL tests.OK.HOL tests.OK.Impred;

symbol ε [a:Set] : (τ a → Prop) → τ a;
symbol εᵢ [a:Set] (p:τ a → Prop) : π (∃ p) → π (p (ε p));
