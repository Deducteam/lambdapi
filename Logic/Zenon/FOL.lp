// encoding of first-order logic

constant symbol κ : TYPE;

constant symbol Prop : TYPE;

symbol ⊤ : Prop;
symbol ⊥ : Prop;
symbol ∧ : Prop → Prop → Prop; notation ∧ infix right 10;
symbol ∨  : Prop → Prop → Prop; notation ∨ infix right 9;
symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 5;
symbol = : κ → κ → Prop; notation = infix 12;
symbol ∀ : (κ → Prop) → Prop; notation ∀ quantifier;
symbol ∃ : (κ → Prop) → Prop; notation ∃ quantifier;

symbol ¬ p ≔ p ⇒ ⊥; notation ¬ prefix 20;
symbol ⇔ p q ≔ (p ⇒ q) ∧ (q ⇒ p); notation ⇔ infix left 10;
symbol ≠ t u ≔ ¬ (t = u); notation ≠ infix 12;

symbol ϵ : Prop → TYPE;
