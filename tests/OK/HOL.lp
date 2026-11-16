// higher-order logic

require open tests.OK.Set;

constant symbol ⤳ : Set → Set → Set; // \leadsto

notation ⤳ infix right 20;

builtin "arr" ≔ ⤳;

rule τ ($a ⤳ $b) ↪ τ $a → τ $b;

injective symbol ⤳d : Π a:Set, (τ a → Set) → Set;

notation ⤳d infix right 20;

rule $a ⤳d λ _,$b.[] ↪ $a ⤳ $b;

rule τ ($a ⤳d λ x,$b.[x]) ↪ Π x:τ $a, τ $b.[x];

// function composition \circ
symbol ∘ [a b c] : τ (b ⤳ c) → τ (a ⤳ b) → τ a → τ c ≔ λ g f x, g (f x);

notation ∘ infix 20;
