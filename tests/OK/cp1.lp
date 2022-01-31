// test computation of critical pairs

require open tests.OK.cp0;

rule a (a $x $y) $z ↪ a $x (a $y $z);
// generates 3 joinable critical pairs
