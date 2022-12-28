// (multi-sorted) First-order logic

require open tests.OK.Set tests.OK.Prop;

// Universal quantification

constant symbol ∀ [a] : (τ a → Prop) → Prop; notation ∀ quantifier; // !! or \forall

rule π (∀ $f) ↪ Π x, π ($f x);

// Existential quantification

constant symbol ∃ [a] : (τ a → Prop) → Prop; notation ∃ quantifier; // ?? or \exists
