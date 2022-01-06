require open Logic.U.Prop;

symbol Prfᶜ p ≔ Prf (¬ ¬ p);

symbol ⇒ᶜ p q ≔ ¬ ¬ p ⇒ ¬ ¬ q; notation ⇒ᶜ infix right 10;

symbol ∧ᶜ p q ≔ ¬ ¬ p ∧ ¬ ¬ q; notation ∧ᶜ infix right 10;

symbol ∨ᶜ p q ≔ ¬ ¬ p ∨ ¬ ¬ q; notation ∨ᶜ infix right 10;

require open Logic.U.Set Logic.U.Quant;

symbol ∀ᶜ [a] p ≔ `∀ x : El a, ¬ ¬ (p x); notation ∀ᶜ quantifier;

symbol ∃ᶜ [a] p ≔ `∃ x : El a, ¬ ¬ (p x); notation ∃ᶜ quantifier;
