// Type of set codes for quantifying other sets (polymorphism)

constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE;

builtin "T" ≔ τ;
