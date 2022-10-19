// Propositional logic

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

// interpretation of propositions in TYPE

injective symbol π : Prop → TYPE; // `p

builtin "P" ≔ π;

// true

constant symbol ⊤ : Prop; // \top

constant symbol top : π ⊤;

// false

constant symbol ⊥ : Prop; // \bot

constant symbol ⊥ₑ [p] : π ⊥ → π p;

// implication

constant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 5; // =>

rule π ($p ⇒ $q) ↪ π $p → π $q;

// negation

symbol ¬ p ≔ p ⇒ ⊥; // ~~ or \neg

// conjunction

constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix left 7; // /\ or \wedge

constant symbol ∧ᵢ [p q] : π p → π q → π (p ∧ q);
symbol ∧ₑ₁ [p q] : π (p ∧ q) → π p;
symbol ∧ₑ₂ [p q] : π (p ∧ q) → π q;

// disjunction

constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix left 6; // \/ or \vee

constant symbol ∨ᵢ₁ [p q] : π p → π (p ∨ q);
constant symbol ∨ᵢ₂ [p q] : π q → π (p ∨ q);
symbol ∨ₑ [p q r] : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

// check that priorities are correctly set
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);
