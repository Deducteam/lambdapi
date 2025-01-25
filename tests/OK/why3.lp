require open tests.OK.Prop tests.OK.Set tests.OK.FOL;

prover "Alt-Ergo";
prover_timeout 2;

opaque symbol test1 p : π p → π p ≔ begin why3 end;

opaque symbol test2 p q : π (p ∧ q) → π p ≔ begin why3 end;

opaque symbol test3 : Π p q, π (p ∧ q) → π p ≔ begin why3 end;

opaque symbol test4 p : π (p ∨ ¬ p) ≔ begin why3 end;

opaque symbol test5 p q : π p → π (p ∨ q) ≔ begin why3 end;

opaque symbol test6 p q : π (p ⇒ q) → π p → π q ≔ begin why3 end;

constant symbol nat:Set;

symbol even : τ nat → Prop;

opaque symbol test7 : π (`∃ n, even n ⇒ even n) ≔ begin why3 end;

opaque symbol test8 a p: π (`∃ x:τ a, p x ⇒ p x) ≔ begin why3 end;

opaque symbol test9 a p : π (¬ (`∃ x:τ a, p x) ⇔ (`∀ x, ¬ (p x))) ≔ begin why3 end;

//constant symbol o:Set;
//rule τ o ↪ Prop;

//opaque symbol test10 a (p:τ(nat ⤳ o)) : π (¬ (`∃ x:τ a, p x) ⇔ (`∀ x, ¬ (p x))) ≔ begin why3 end;

//opaque symbol test10 : π (`∃ p, p ⇒ p) ≔ begin why3 end;
