require open tests.OK.bool;

// Data type of natural numbers.

constant symbol N : TYPE;

constant symbol z : N;
constant symbol s : N → N;

// Enabling built-in natural number literal, and example.

builtin "0"  ≔ z;
builtin "+1" ≔ s;

symbol forty_two ≔ 42;

// Addition function.

symbol + : N → N → N;
notation + infix left 6;

rule z      + $n     ↪ $n
with (s $m) + $n     ↪ s ($m + $n)
with $m     + z      ↪ $m
with $m     + (s $n) ↪ s ($m + $n);

// Multiplication function.

symbol × : N → N → N;
notation × infix left 7;

rule z      × _      ↪ z
with (s $m) × $n     ↪ $n + $m × $n
with _      × z      ↪ z
with $m     × (s $n) ↪ $m + $m × $n;

// Doubling function.

symbol double n ≔ n × 2;

// Equality function.

symbol eq_nat : N → N → B;

rule eq_nat z      z      ↪ true
with eq_nat (s $m) (s $n) ↪ eq_nat $m $n
with eq_nat z      (s _)  ↪ false
with eq_nat (s _)  z      ↪ false;

// Less than function.

symbol le_nat : N → N → B;

rule le_nat z      z      ↪ false
with le_nat z      (s _)  ↪ true
with le_nat (s $m) (s $n) ↪ le_nat $m $n;
