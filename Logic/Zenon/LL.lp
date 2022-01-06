// deep encoding of Zenon LL proofs

require open Logic.Zenon.FOL;
 
symbol R⊥ : ϵ ⊥ → ϵ ⊥;
symbol R¬⊤ : ϵ (¬ ⊤) → ϵ ⊥;
symbol Rax p : ϵ p → ϵ (¬ p) → ϵ ⊥;
symbol R≠ t : ϵ (¬ (t = t)) → ϵ ⊥;
symbol R= t u : ϵ (t = u) → ϵ (¬ (u = t)) → ϵ ⊥;
symbol Rcut p : (ϵ p → ϵ ⊥) → (ϵ (¬ p) → ϵ ⊥) → ϵ ⊥;
symbol R¬¬ p : (ϵ p → ϵ ⊥) → ϵ (¬ (¬ p)) → ϵ ⊥;
symbol R∧ p q : (ϵ p → ϵ q → ϵ ⊥) → ϵ (p ∧ q) → ϵ ⊥;
symbol R∨ p q : (ϵ p → ϵ ⊥) → (ϵ q → ϵ ⊥) → ϵ (p ∨ q) → ϵ ⊥;
symbol R⇒ p q :
  (ϵ (¬ p) → ϵ ⊥) → (ϵ q → ϵ ⊥) → ϵ (p ⇒ q) → ϵ ⊥;
symbol R⇔ p q : (ϵ (¬ p) → ϵ (¬ q) → ϵ ⊥)
  → (ϵ p → ϵ q → ϵ ⊥) → ϵ (p ⇔ q) → ϵ ⊥;
symbol R¬∧ p q :
  (ϵ (¬ p) → ϵ ⊥) → (ϵ (¬ q) → ϵ ⊥) → ϵ (¬ (p ∧ q)) → ϵ ⊥;
symbol R¬∨ p q :
  (ϵ (¬ p) → ϵ (¬ q) → ϵ ⊥) → ϵ (¬ (p ∨ q)) → ϵ ⊥;
symbol R¬⇒ p q :(ϵ p → ϵ (¬ q) → ϵ ⊥) → ϵ (¬ (p ⇒ q)) → ϵ ⊥ ;
symbol R¬⇔ p q :
  (ϵ (¬ p) → ϵ q → ϵ ⊥) → (ϵ p → ϵ (¬ q) → ϵ ⊥)
  → ϵ (¬ (p ⇔ q)) → ϵ ⊥;
symbol R∃ p : (Π x, ϵ (p x) → ϵ ⊥) → ϵ (∃ p) → ϵ ⊥;
symbol R∀ p t : (ϵ (p t) → ϵ ⊥) → ϵ (∀ p) → ϵ ⊥;
symbol R¬∃ p t : (ϵ (¬ (p t)) → ϵ ⊥) → ϵ (¬ (∃ p)) → ϵ ⊥;
symbol R¬∀ p : (Π x, ϵ (¬ (p x)) → ϵ ⊥) → ϵ (¬ (∀ p)) → ϵ ⊥;
symbol Rσ p t u :
  (ϵ (¬ (t = u)) → ϵ ⊥) → (ϵ (p u) → ϵ ⊥) → ϵ (p t) → ϵ ⊥;
symbol R≡r p t u :
  (ϵ (p u) → ϵ ⊥) → ϵ (p t) → ϵ (t = u) → ϵ ⊥;
symbol R≡l p t u :
  (ϵ (p u) → ϵ ⊥) → ϵ (p t) → ϵ (u = t) → ϵ ⊥;
