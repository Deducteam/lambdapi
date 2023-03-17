require open tests.OK.logic;
require open tests.OK.natural;

prover "Alt-Ergo";
prover_timeout 2;

symbol o : U;
rule T o ↪ Prop;

constant symbol nat: U;
symbol even (_: T nat): Prop;

// Test a quantification on the boolean type
opaque symbol thm_ex : P (ex o (λ p: T o, imp p p))
≔ begin 
  why3; 
end;

// Quantification on a type symbol
opaque symbol thm_even : P (ex nat (λ n: T nat, imp (even n) (even n)))
≔ begin
  why3;
end;

// Quantification on a type variable
opaque symbol tyvar (a: U) (q: T a → T o): P (ex a (λ n: T a, imp (q n) (q n)))
≔ begin
  why3;
end; 

