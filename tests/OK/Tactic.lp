// define a type representing Lambdapi tactics

require open tests.OK.String tests.OK.Option tests.OK.List;

constant symbol Tactic : TYPE;

// mandatory builtins

constant symbol #admit : Tactic;
builtin "admit" ≔ #admit;

symbol & : Tactic → Tactic → Tactic;
builtin "and" ≔ &;
notation & infix right 10;

constant symbol #apply [p] : π p → Tactic;
builtin "apply" ≔ #apply;

constant symbol #assume : String → Tactic;
builtin "assume" ≔ #assume;

constant symbol #fail : Tactic;
builtin "fail" ≔ #fail;

constant symbol #generalize : Π [a], τ a → Tactic;
builtin "generalize" ≔ #generalize;

constant symbol #have : String → Prop → Tactic;
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

constant symbol #simplify : Tactic;
builtin "simplify" ≔ #simplify;

constant symbol #simplify_beta : Tactic;
builtin "simplify rule off" ≔ #simplify_beta;

constant symbol #solve : Tactic;
builtin "solve" ≔ #solve;

constant symbol #symmetry : Tactic;
builtin "symmetry" ≔ #symmetry;

constant symbol #try : Tactic → Tactic;
builtin "try" ≔ #try;

constant symbol #why3 : Tactic;
builtin "why3" ≔ #why3;

// defined tactics

symbol nothing ≔ #try #fail;

require open tests.OK.Nat;

symbol times : ℕ → Tactic → Tactic;
notation times infix 20;

rule 0 times _ ↪ nothing
with $n +1 times $t ↪ $t & $n times $t;
