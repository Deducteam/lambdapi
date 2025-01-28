// (multi-sorted) First-order logic

require open tests.OK.Set tests.OK.Prop;

// Universal quantification

constant symbol ∀ [a] : (τ a → Prop) → Prop;

builtin "all" ≔ ∀;
notation ∀ quantifier; // !! or \forall

rule π (∀ $f) ↪ Π x, π ($f x);

// Existential quantification

constant symbol ∃ [a] : (τ a → Prop) → Prop; notation ∃ quantifier; // ?? or \exists

builtin "ex" ≔ ∃;

constant symbol ∃ᵢ [a] p (x:τ a) : π (p x) → π (∃ p);
symbol ∃ₑ [a] p : π (∃ p) → Π q, (Π x:τ a, π (p x) → π q) → π q;

rule ∃ₑ _ (∃ᵢ _ $x $px) _ $f ↪ $f $x $px;
