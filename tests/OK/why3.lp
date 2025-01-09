require open tests.OK.logic;
require open tests.OK.natural;

prover "Alt-Ergo";
prover_timeout 2;

opaque symbol tautology : Π (a : Prop), P a → P a
≔ begin
    why3;
end;

opaque symbol thm_and1 : Π (a b : Prop), P ({|and|} a b) → P a
≔ begin
    why3;
end;

opaque symbol thm_and2 : Π (a b : Prop), P ({|and|} a b) → P b
≔ begin
    why3;
end;

opaque symbol excluded_middle : Π (a : Prop), P (or a (not a))
≔ begin
    why3;
end;

opaque symbol thm_or1 : Π (a b : Prop), P a → P (or a b)
≔ begin
    why3;
end;

opaque symbol thm_or2 : Π (a b : Prop), P b → P (or a b)
≔ begin
    why3;
end;

opaque symbol thm_imp : Π (a b : Prop), P (imp a b) → P a → P b
≔ begin
    why3;
end;

symbol o : U;
rule T o ↪ Prop;

constant symbol nat: U;
symbol even (_: T nat): Prop;

opaque symbol thm_ex : P (ex o (λ p: T o, imp p p))
≔ begin 
  why3;
end;

opaque symbol thm_even : P (ex nat (λ n: T nat, imp (even n) (even n)))
≔ begin
  why3;
end;

opaque symbol tyvar (a: U) (q: T a → T o): P (ex a (λ n: T a, imp (q n) (q n)))
≔ begin
  why3;
end; 
