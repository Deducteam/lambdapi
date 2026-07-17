require open tests.OK.Set tests.OK.Prop;

constant symbol L:TYPE;

builtin "Level" ≔ L;

constant symbol prop:L;
constant symbol set_:L;

injective symbol U:L → TYPE;

builtin "Univ" ≔ U;

rule U prop ↪ Prop
with U set_ ↪ Set;

symbol η:Π [l:L], U l → TYPE; // \eta

builtin "Type" ≔ η;

rule η [prop] ↪ π
with η [set_] ↪ τ;

unif_rule η $a ≡ π $b ↪ [$a ≡ $b];
unif_rule η $a ≡ τ $b ↪ [$a ≡ $b];

require open tests.OK.FOL;

unif_rule η $a ≡ Π x:$b, π $c.[x] ↪ [$a ≡ `∀ x:$b, $c.[x]];
