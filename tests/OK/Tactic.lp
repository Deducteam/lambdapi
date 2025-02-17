// define a type representing Lambdapi tactics

require open tests.OK.Set tests.OK.Prop tests.OK.String tests.OK.Option
             tests.OK.List;

constant symbol Tactic : TYPE;

constant symbol #admit : Tactic;
builtin "admit" ≔ #admit;

symbol & : Tactic → Tactic → Tactic;
builtin "and" ≔ &;
notation & infix right 10;

constant symbol #apply [p] : π p → Tactic;
builtin "apply" ≔ #apply;

constant symbol #assume : τ (list string) → Tactic;
builtin "assume" ≔ #assume;

constant symbol #fail : Tactic;
builtin "fail" ≔ #fail;

constant symbol #generalize : Π [a], τ a → Tactic;
builtin "generalize" ≔ #generalize;

constant symbol #have : String → Π p, π p → Tactic;
builtin "have" ≔ #have;

constant symbol #induction : Tactic;
builtin "induction" ≔ #induction;

constant symbol #orelse : Tactic → Tactic → Tactic;
builtin "orelse" ≔ #orelse;

constant symbol #refine [p] : π p → Tactic;
builtin "refine" ≔ #refine;

constant symbol #reflexivity : Tactic;
builtin "reflexivity" ≔ #reflexivity;

constant symbol #remove : Π [a], π a → Tactic;
builtin "remove" ≔ #remove;

constant symbol #repeat : Tactic → Tactic;
builtin "repeat" ≔ #repeat;

constant symbol #rewrite [p] : π p → Tactic;
builtin "rewrite" ≔ #rewrite;

constant symbol #set : String → Π [a], τ a → Tactic;
builtin "set" ≔ #set;

constant symbol #simplify : /* Π [a], τ a → */ Tactic;
builtin "simplify" ≔ #simplify;

constant symbol #solve : Tactic;
builtin "solve" ≔ #solve;

constant symbol #symmetry : Tactic;
builtin "symmetry" ≔ #symmetry;

constant symbol #try : Tactic → Tactic;
builtin "try" ≔ #try;

constant symbol #why3 : /*τ (option string) →*/ Tactic;
builtin "why3" ≔ #why3;

/*****************************************************************************/

symbol nothing ≔ #try #fail;

require open tests.OK.Nat;

symbol * : ℕ → Tactic → Tactic;
notation * infix 20;

rule 0 * _ ↪ nothing
with $n +1 * $t ↪ $t & ($n * $t);

require open tests.OK.Eq;

symbol lemma x y z t : π (((x + y) + z) + t = x + (y + (z + t))) ≔
begin
  assume x y z t;
  //rewrite addnA; rewrite addnA; reflexivity
  compute 2 * #rewrite addnA;
  eval 2 * #rewrite addnA & #reflexivity
end;
