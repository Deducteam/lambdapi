// deep encoding of natural deduction proofs

require open Logic.Zenon.FOL;

symbol ⊥E : ϵ ⊥ → Π r, ϵ r;

symbol ⊤I : ϵ ⊤;

symbol ∧I p q : ϵ p → ϵ q → ϵ (p ∧ q);
symbol ∧El p q : ϵ (p ∧ q) → ϵ p;
symbol ∧Er p q : ϵ (p ∧ q) → ϵ q;

symbol ∨Il p q : ϵ p → ϵ (p ∨ q);
symbol ∨Ir p q : ϵ q → ϵ (p ∨ q);
symbol ∨E p q :
  ϵ (p ∨ q) → Π r, (ϵ p → ϵ r) → (ϵ q → ϵ r) → ϵ r;

symbol ⇒I p q : (ϵ p → ϵ q) → ϵ (p ⇒ q);
symbol ⇒E p q : ϵ (p ⇒ q) → ϵ p → ϵ q;

symbol =I t : ϵ (t = t);
symbol =E t u : ϵ (t = u) → Π p, ϵ (p t) → ϵ (p u);

symbol ∀I p : (Π x, ϵ (p x)) → ϵ (∀ p);
symbol ∀E p x : ϵ (∀ p) → ϵ (p x);

symbol ∃I p x : ϵ (p x) → ϵ (∃ p);
symbol ∃E p : ϵ (∃ p) → Π r, (Π x, ϵ (p x) → ϵ r) → ϵ r;
