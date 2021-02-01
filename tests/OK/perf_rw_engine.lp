// A simple loop to benchmark the rewriting engine
require open tests.OK.nat;

symbol upper ≔ 3000;

symbol loop : N → N → N;
rule loop (s $x) 0      ↪ loop $x upper
with loop $x     (s $y) ↪ loop $x $y;

compute loop upper upper;
