// Test the addition of axioms in the signature when metavariables remain

constant symbol Type: TYPE;
injective symbol El: Type → TYPE;

constant symbol Prop: TYPE;
injective symbol Prf: Prop → TYPE;

constant symbol prop: Type;
rule El prop ↪ Prop;

constant symbol ι: Type;
constant symbol zero: El ι;

// A simple independant axiom
symbol pred: El ι → Prop;
symbol f (n: El ι): Prf (pred n) → Prop;
symbol f_zero: Prf (f zero _)
begin
  // Adds an axiom [ax_?]
admit;

// Two metas, one depending on the other
symbol pred2 (n: El ι): Prf (pred n) → Prop;
symbol g (n: El ι) (π: Prf (pred n)) (_: Prf (pred2 n π)): Prop;
symbol g_zero: Prf (g zero _ _)
begin
  // Adds two axioms
admit;
