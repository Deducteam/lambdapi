// Propositional logic

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

// interpretation of propositions in TYPE

injective symbol π : Prop → TYPE; // `p

builtin "P" ≔ π;

// true

constant symbol ⊤ : Prop; // \top

builtin "top" ≔ ⊤;

constant symbol ⊤ᵢ : π ⊤;

// false

constant symbol ⊥ : Prop; // \bot

builtin "bot" ≔ ⊥;

constant symbol ⊥ₑ [p] : π ⊥ → π p;

// implication

constant symbol ⇒ : Prop → Prop → Prop;

builtin "imp" ≔ ⇒;

notation ⇒ infix right 5; // =>

rule π ($p ⇒ $q) ↪ π $p → π $q;

// negation

symbol ¬ p ≔ p ⇒ ⊥; // ~~ or \neg

builtin "not" ≔ ¬;
notation ¬ prefix 100;

// conjunction

constant symbol ∧ : Prop → Prop → Prop; // /\ or \wedge

builtin "and" ≔ ∧;
notation ∧ infix left 7;

constant symbol ∧ᵢ [p q] : π p → π q → π (p ∧ q);
symbol ∧ₑ₁ [p q] : π (p ∧ q) → π p;
symbol ∧ₑ₂ [p q] : π (p ∧ q) → π q;

// disjunction

constant symbol ∨ : Prop → Prop → Prop; // \/ or \vee

builtin "or" ≔ ∨;

notation ∨ infix left 6;
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);

constant symbol ∨ᵢ₁ [p q] : π p → π (p ∨ q);
constant symbol ∨ᵢ₂ [p q] : π q → π (p ∨ q);
symbol ∨ₑ [p q r] : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

// equivalence

symbol ⇔ x y ≔ x ⇒ y ∧ y ⇒ x;

builtin "eqv" ≔ ⇔;

notation ⇔ infix right 30;
