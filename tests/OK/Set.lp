constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

builtin "T" ≔ τ;

symbol ⤳ : Set → Set → Set; // \leadsto

notation ⤳ infix 20;

rule τ($a ⤳ $b) ↪ τ $a → τ $b;
