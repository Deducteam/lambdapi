require open tests.OK.natural;

symbol power : N → N → N;
rule power _      0  ↪ 1
with power $x (s $y) ↪ $x × (power $x $y);

symbol fact : N → N;
rule fact 0      ↪ 1
with fact (s $x) ↪ (s $x) × (fact $x);

compute power 5 5;
compute fact 7;
