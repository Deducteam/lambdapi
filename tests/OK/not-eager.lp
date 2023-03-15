// Tests evaluation laziness.  If too eager, 99! will be computed...
require open tests.OK.natural;

symbol l : N → N → N;
rule l $x      0     ↪ l 0 $x
with l 0       _     ↪ 0
with l (s $x) (s $y) ↪ l $x $y;

symbol fact : N → N;
rule fact 0      ↪ 1
with fact (s $x) ↪ (s $x) × (fact $x);

compute l 0 (s (fact 99));
// Second 's' is discovered by rule 2
compute l (s (s (fact 99))) 1;
