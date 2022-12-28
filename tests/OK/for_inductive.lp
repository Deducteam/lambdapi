constant symbol Prop : TYPE;      // Type of propositions
builtin "Prop" ≔ Prop;

injective symbol π : Prop → TYPE; // Interpretation of propositions in TYPE
builtin "P" ≔ π;

constant symbol Set : TYPE;       // Type of set codes
injective symbol τ : Set → TYPE;  // Interpretation of set codes in TYPE
