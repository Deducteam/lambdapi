require open tests.OK.Set;

symbol ⤳ : Set → Set → Set; // \leadsto

notation ⤳ infix right 20;

rule τ ($a ⤳ $b) ↪ τ $a → τ $b;

symbol ⤳d : Π a:Set, (τ a → Set) → Set;

notation ⤳d infix right 20;

rule τ ($a ⤳d (λ x,$b.[x])) ↪ Π x:τ $a, τ $b.[x];
