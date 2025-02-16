// define a type representing Lambdapi tactics

require open tests.OK.Set tests.OK.Prop;

constant symbol Tactic : TYPE;

constant symbol #admit : Tactic;
builtin "admit" ≔ #admit;

symbol #and : Tactic → Tactic → Tactic;
builtin "and" ≔ #and;
notation #and infix right 10;

constant symbol #apply [p] : π p → Tactic;
builtin "apply" ≔ #apply;

//constant symbol #assume : ? → Tactic;
//builtin "assume" ≔ #assume;

constant symbol #fail : Tactic;
builtin "fail" ≔ #fail;

//constant symbol #generalize : Ident → Tactic;
//builtin "generalize" ≔ #generalize;

//constant symbol #have : Ident → Term → Tactic;
//builtin "have" ≔ #have;

constant symbol #induction : Tactic;
builtin "induction" ≔ #induction;

constant symbol #orelse : Tactic → Tactic → Tactic;
builtin "orelse" ≔ #orelse;

constant symbol #refine [p] : π p → Tactic;
builtin "refine" ≔ #refine;

constant symbol #reflexivity : Tactic;
builtin "reflexivity" ≔ #reflexivity;

//constant symbol #remove : Ident → Tactic;
//builtin "remove" ≔ #remove;

constant symbol #repeat : Tactic → Tactic;
builtin "repeat" ≔ #repeat;

constant symbol #rewrite [p] : π p → Tactic;
builtin "rewrite" ≔ #rewrite;

//constant symbol #set : Ident → Term → Tactic;
//builtin "set" ≔ #set;

constant symbol #simplify : /* Option Ident → */ Tactic;
builtin "simplify" ≔ #simplify;

constant symbol #solve : Tactic;
builtin "solve" ≔ #solve;

constant symbol #symmetry : Tactic;
builtin "symmetry" ≔ #symmetry;

constant symbol #try : Tactic → Tactic;
builtin "try" ≔ #try;

constant symbol #why3 : /*Ident Option →*/ Tactic;
builtin "why3" ≔ #why3;

/*****************************************************************************/

symbol #nothing ≔ #repeat #fail;

require open tests.OK.Nat;

symbol #times : ℕ → Tactic → Tactic;
notation #times infix 20;

rule 0 #times _ ↪ #nothing
with $n +1 #times $t ↪ $t #and ($n #times $t);

require open tests.OK.Eq;

symbol lemma x y z t : π (((x + y) + z) + t = x + (y + (z + t))) ≔
begin
  assume x y z t;
  //rewrite addnA; rewrite addnA; reflexivity
  compute 2 #times #rewrite addnA;
  eval 2 #times #rewrite addnA #and #reflexivity
end;
