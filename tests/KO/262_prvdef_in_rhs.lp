require tests.OK.{|262_parsing|} as D;

symbol g : D.A → D.A;

// Foreign private symbols are forbidden in right-hand-sides
rule g $X ↪ D.gdouble $X;
