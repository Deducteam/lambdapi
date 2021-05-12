// Performance on non linear tests.
require open tests.OK.nat;

symbol upper ≔ 500;

symbol loop : N → N → N → N;
rule loop $x $x (s $y) ↪ loop $x $x $y
with loop (s $x) _ 0   ↪ loop $x $x upper;

compute loop upper (s upper) upper; // quick
compute loop upper upper upper;     // long
