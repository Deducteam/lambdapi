require open tests.OK.boolean;

// Data type of natural numbers.

constant symbol N : TYPE;

constant symbol z : N;
constant symbol s : N → N;

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

// Enabling parsing of decimal notation

symbol n1 ≔ s z;
symbol n2 ≔ s n1;
symbol n3 ≔ s n2;
symbol n4 ≔ s n3;
symbol n5 ≔ s n4;
symbol n6 ≔ s n5;
symbol n7 ≔ s n6;
symbol n8 ≔ s n7;
symbol n9 ≔ s n8;
symbol n10 ≔ s n9;

builtin "0"  ≔ z;
builtin "1" ≔ n1;
builtin "2" ≔ n2;
builtin "3" ≔ n3;
builtin "4" ≔ n4;
builtin "5" ≔ n5;
builtin "6" ≔ n6;
builtin "7" ≔ n7;
builtin "8" ≔ n8;
builtin "9" ≔ n9;
builtin "10" ≔ n10;

builtin "+" ≔ +;
builtin "*" ≔ ×;

symbol forty_two ≔ 42;

assert ⊢ forty_two
  ≡ let two ≔ s(s z) in
    let four ≔ two + two in
    let ten ≔ four + four + two in
    four × ten + two;

// Enabling printing of decimal notation

builtin "nat_zero" ≔ z;
builtin "nat_succ" ≔ s;

compute 4 + 5;

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
