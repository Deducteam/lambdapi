// type of type codes

constant symbol Set : TYPE;

builtin "Set" ≔ Set;

constant symbol ι : Set;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

builtin "El" ≔ τ;

// We assume that sets are non-empty

symbol el a : τ a;
