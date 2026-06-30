// Type of set codes for quantifying over sets (polymorphism)

constant symbol Set : TYPE;

constant symbol ι : Set;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

builtin "T" ≔ τ;

// We assume that sets are non-empty

symbol el a : τ a;
