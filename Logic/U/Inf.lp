require open Logic.U.Set Logic.U.Prop;

constant symbol zero : El ι; builtin "0" ≔ zero;

constant symbol succ : El ι → El ι; builtin "+1" ≔ succ;

symbol pred : El ι → El ι;

rule pred 0 ↪ 0
with pred (succ $x) ↪ $x;

symbol positive : El ι → Prop;

rule positive 0 ↪ ⊥
with positive (succ _) ↪ ⊤;
