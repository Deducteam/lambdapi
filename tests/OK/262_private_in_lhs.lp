// Using private symbols in LHSs
require tests.OK.{|262_parsing|} as D;

symbol f : D.A → D.A;

rule f (D.g $x) ↪ $x
with f (D.gdouble $x) ↪ f $x;
