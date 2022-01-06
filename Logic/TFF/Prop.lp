// Propositional logic

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

// Interpretation of propositions in TYPE

injective symbol π : Prop → TYPE;

builtin "P" ≔ π;

// True

constant symbol ⊤ : Prop;

constant symbol top : π ⊤;

// False

constant symbol ⊥ : Prop;

constant symbol ⊥ₑ p : π ⊥ → π p;

// Conjunction

constant symbol ∧ : Prop → Prop → Prop; // \wedge

notation ∧ infix left 7;

constant symbol ∧ᵢ p q : π p → π q → π (p ∧ q);
symbol ∧ₑ₁ p q : π (p ∧ q) → π p;
symbol ∧ₑ₂ p q : π (p ∧ q) → π q;

// Disjunction

constant symbol ∨ : Prop → Prop → Prop; // \vee

notation ∨ infix left 6;

constant symbol ∨ᵢ₁ p q : π p → π (p ∨ q);
constant symbol ∨ᵢ₂ p q : π q → π (p ∨ q);
symbol ∨ₑ p q r : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

// check that priorities are correctly set
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);

// Implication

constant symbol ⇒ : Prop → Prop → Prop; // =>

notation ⇒ infix right 5;

rule π ($p ⇒ $q) ↪ π $p → π $q;

// Negation

symbol ¬ p ≔ p ⇒ ⊥;
