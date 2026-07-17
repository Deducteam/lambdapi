// define a type representing Lambdapi tactics

require open tests.OK.String tests.OK.Univ;

// mandatory builtins

constant symbol Tactic : TYPE;
builtin "Tactic" ≔ Tactic;

constant symbol #admit : Tactic;
builtin "admit" ≔ #admit;

constant symbol #all_hyps: (Π [l] [a:U l], η a → Tactic) → Tactic;
builtin "all_hyps" ≔ #all_hyps;

constant symbol #apply: Π [l] [a:U l], η a → Tactic;
builtin "apply" ≔ #apply;

constant symbol #assume : String → Π [l], Π [a:U l], (η a → Tactic) → Tactic;
builtin "assume" ≔ #assume;

constant symbol #assumption : Tactic;
builtin "assumption" ≔ #assumption;

constant symbol #change: Π [l] [a:U l], η a → Tactic;
builtin "change" ≔ #change;

constant symbol & : Tactic → Tactic → Tactic;
builtin "compose" ≔ &;
notation & infix right 10;

constant symbol #fail : Tactic;
builtin "fail" ≔ #fail;

constant symbol #first_hyp: (Π [l] [a:U l], η a → Tactic) → Tactic;
builtin "first_hyp" ≔ #first_hyp;

constant symbol #focus : String → Tactic;
builtin "focus" ≔ #focus;

constant symbol #generalize : Π [l] [a:U l], η a → Tactic;
builtin "generalize" ≔ #generalize;

constant symbol #have : String → Prop → Tactic;
builtin "have" ≔ #have;

constant symbol #induction : Tactic;
builtin "induction" ≔ #induction;

constant symbol #orelse : Tactic → Tactic → Tactic;
builtin "orelse" ≔ #orelse;

constant symbol #print : String → Tactic;
builtin "print" ≔ #print;

constant symbol #refine: String → Tactic;
builtin "refine" ≔ #refine;

constant symbol #reflexivity : Tactic;
builtin "reflexivity" ≔ #reflexivity;

constant symbol #remove : Π [l] [a:U l], η a → Tactic;
builtin "remove" ≔ #remove;

constant symbol #repeat : Tactic → Tactic;
builtin "repeat" ≔ #repeat;

 symbol #rewrite : String → String → Π [l] [a:U l], η a → Tactic;
builtin "rewrite" ≔ #rewrite;

constant symbol #set : String → Π [l] [a:U l], η a → Tactic;
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
