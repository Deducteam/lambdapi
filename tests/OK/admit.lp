// Test the addition of axioms in the signature when metavariables remain

constant symbol Type: TYPE;
injective symbol El: Type → TYPE;

constant symbol Prop: TYPE;
injective symbol Prf: Prop → TYPE;

constant symbol prop: Type;
rule El prop ↪ Prop;

constant symbol ι: Type;

// A simple independant axiom
symbol prop1: Prop;
symbol f: Prf prop1 → El ι;
symbol π_f: Prf (f _)
begin
  // Adds an axiom [ax_?]
admit;

// Two metas, one depending on the other
symbol prop2: Prf prop1 → Prop;
symbol g (π: Prf prop1) (_: Prf (prop2 π)): Prop;
symbol π_g: Prf (g _ ?named_meta)
begin
  // Adds two axioms
admit;
