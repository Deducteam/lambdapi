require open tests.preuves_Ledein.notation

// Conjunction
constant symbol {|and|} : Prop ⇒ Prop ⇒ Prop
set infix left 7 "∧" ≔ {|and|}
constant symbol and_intro p q : π p ⇒ π q ⇒ π (p ∧ q)
symbol and_elim_left p q  : π (p ∧ q) ⇒ π p
symbol and_elim_right p q : π (p ∧ q) ⇒ π q

// Disjunction
constant symbol or : Prop ⇒ Prop ⇒ Prop
set infix left 6 "∨" ≔ or
constant symbol or_intro_left p q  : π p ⇒ π (p ∨ q)
constant symbol or_intro_right p q : π q ⇒ π (p ∨ q)
symbol or_elim p q r : π (p ∨ q) ⇒ (π p ⇒ π r) ⇒ (π q ⇒ π r) ⇒ π r

assert λx y z,x∨y∧z ≡ λx y z,x∨(y∧z) // check that propositions are parsed correctly
  
// False
set declared "⊥"
constant symbol ⊥ : Prop
symbol false_elim p : π ⊥ ⇒ π p

// Negation
set declared "¬"
constant symbol ¬ : Prop ⇒ Prop
constant symbol not_intro p : (π p ⇒ π ⊥) ⇒ π (¬p)
symbol not_elim  p : π (¬ p) ⇒ π p ⇒ π ⊥

// Intro and Elimination of imp
constant symbol imp : Prop ⇒ Prop ⇒ Prop
constant symbol imp_intro p q : (π p ⇒ π q) ⇒ π (imp p q)
symbol imp_elim  p q : π (imp p q) ⇒ π p ⇒ π q

// Universal quantification
constant symbol all {a} : (τ a ⇒ Prop) ⇒ Prop
rule π (@all &a &f) → ∀x:τ &a, π (&f x)

// Existential quantification
set declared "∃"
constant symbol ∃ {a} : (τ a ⇒ Prop) ⇒ Prop
constant symbol ex_intro {a} p (x:τ a) : π (p x) ⇒ π (∃ p)
symbol ex_elim {a} p q : π (∃ p) ⇒ (∀x:τ a, π (p x) ⇒ π q) ⇒ π q

// Set builtins for the rewrite tactic
set builtin "all"   ≔ all
set builtin "bot"   ≔ ⊥
//set builtin "top"   ≔ top
set builtin "imp"   ≔ imp
set builtin "and"   ≔ {|and|}
set builtin "or"    ≔ or
set builtin "not"   ≔ ¬
