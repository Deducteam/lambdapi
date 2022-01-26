// test computation of critical pairs

require open tests.OK.cp0;

rule a $x (a $y $z) ↪ a (a $x $y) $z;
// generates 5 critical pairs, 2 of which are not joinable
