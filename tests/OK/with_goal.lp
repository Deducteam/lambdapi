require open tests.OK.Prop tests.OK.Set tests.OK.FOL tests.OK.Univ;
require open tests.OK.Tactic;

constant symbol T: Set;
constant symbol P: τ T → Prop;

sequential symbol prove: Prop → Tactic;
rule prove (@∀ $T $P) ↪ #assume "x" (λ (x: τ $T), prove ($P x))
with prove ($P ⇒ $Q) ↪ #assume "h" (λ (h: π $P), prove $Q)
with prove _ ↪ #print "" & #assumption;

symbol test : Π x:τ T,  π (P x) → π (P x) ≔
begin
debug +tu;
  eval (#with_goal [prop] (λ (g: U prop), #set "g1" [prop] g & #print "" & prove g));
end;
