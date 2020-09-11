symbol A : TYPE;
symbol a: A;
symbol f: A → A;


symbol g: Π(x:A), A;

definition id : A → A ≔ λ(x: A), x;
definition id2 (x: A) ≔ x;

rule g $x ↪ f $x;

// A one line comment

/* A multiline
comment */

symbol plus: A → A → A;
set infix left 6 "pl" ≔ plus;

assert a pl a: A;
