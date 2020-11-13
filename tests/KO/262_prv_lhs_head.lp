require tests.OK.{|262_parsing|} as D;

// Defining a rule with a foreign private symbol as head is forbidden
rule D.f $X ↪ $X;
