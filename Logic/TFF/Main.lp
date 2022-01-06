// (multi-sorted) First-order logic

require open Logic.TFF.Set Logic.TFF.Prop;

// Universal quantification

constant symbol ∀ [a] : (τ a → Prop) → Prop;

notation ∀ quantifier;

rule π (∀ $f) ↪ Π x, π ($f x);

// Existential quantification

constant symbol ∃ [a] : (τ a → Prop) → Prop;

notation ∃ quantifier;

constant symbol ∃ᵢ [a] p (x:τ a) : π (p x) → π (∃ p);
symbol ∃ₑ [a] p : π (∃ p) → Π q, (Π x:τ a, π (p x) → π q) → π q;

rule ∃ₑ _ (∃ᵢ _ $x $px) _ $f ↪ $f $x $px;
