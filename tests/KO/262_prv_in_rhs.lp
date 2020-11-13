require tests.OK.{|262_parsing|} as D;

symbol g : D.A → D.A;

// Foreign protected symbols are forbidden in right-hand-sides
rule g $X ↪ D.g $X;
