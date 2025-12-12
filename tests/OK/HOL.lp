require open tests.OK.Set;

symbol ⤳ : Set → Set → Set; // \leadsto

notation ⤳ infix right 20;

rule τ ($x ⤳ $y) ↪ τ $x → τ $y;
