require open tests.OK.Set tests.OK.Prop;

constant symbol L:TYPE;

builtin "Level" ≔ L;

constant symbol prop:L;
constant symbol set_:L;

injective symbol U:L → TYPE;

builtin "Univ" ≔ U;

rule U prop ↪ Prop
with U set_ ↪ Set;

symbol ε:Π [l:L], U l → TYPE;

builtin "Type" ≔ ε;

rule ε [prop] $a ↪ π $a
with ε [set_] $a ↪ τ $a;

unif_rule ε $a ≡ π $b ↪ [$a ≡ $b];
unif_rule ε $a ≡ τ $b ↪ [$a ≡ $b];

require open tests.OK.FOL;

unif_rule ε $a ≡ Π x:$b, π $c.[x] ↪ [$a ≡ `∀ x:$b, $c.[x]];
