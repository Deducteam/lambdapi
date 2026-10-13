require open tests.OK.Set;
require open tests.OK.Univ;

require open tests.OK.String;

constant symbol tactic: Set;
symbol Tactic : TYPE ≔ τ tactic;
builtin "Tactic" ≔ Tactic;

constant symbol #assume: String → Π [l], Π [a:U l], (@η l a → Tactic) → Tactic;
builtin "assume" ≔ #assume;
constant symbol #fail : Tactic;
builtin "fail" ≔ #fail;

symbol #bug1: Tactic ≔
  #assume "q" [prop] (λ (eh: π ⊤), #fail);

symbol #bug2 (T: Set): Tactic ≔
  #assume "q" [set_] (λ (eh: τ T), #fail);
