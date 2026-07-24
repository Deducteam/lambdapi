symbol Prop : TYPE;
injective symbol Prf : Prop → TYPE;
builtin "Prop" ≔ Prop;
builtin "Prf" ≔ Prf;

symbol Set : TYPE; 
injective symbol τ : Set → TYPE;
injective symbol τ' : Prop → TYPE;

(a:Set) inductive L:TYPE ≔
| nil : L a
| cons : τ a → L a → L a;

/*
debug +sriu;
verbose 3;
flag "print_meta_types" on;
flag "print_implicits" on;
*/

(a:Set) (b:Prop) inductive 𝕃:TYPE ≔
| □  : 𝕃 a b
| ⸬  : τ a → τ' b → 𝕃 a b → 𝕃 a b;
