require open tests.OK.Set tests.OK.Prop;

constant symbol L:TYPE;

builtin "Level" ≔ L;

constant symbol prop:L;
constant symbol set_:L;

injective symbol U:L → TYPE;

builtin "Univ" ≔ U;

rule U prop ↪ Prop
with U set_ ↪ Set;

injective symbol η:Π [l:L], U l → TYPE; // \eta

builtin "Type" ≔ η;

rule @η prop ↪ π
with @η set_ ↪ τ;

unif_rule @η $l $a ≡ π $b ↪ [$l ≡ prop; $a ≡ $b];
unif_rule @η $l $a ≡ τ $b ↪ [$l ≡ set_; $a ≡ $b];

require open tests.OK.FOL;

unif_rule @η $l $a ≡ Π x:$b, π $c.[x] ↪ [$l ≡ prop; $a ≡ `∀ x:$b, $c.[x]];

require open tests.OK.HOL;

unif_rule @η $l $a ≡ Π _:τ $b, τ $c.[] ↪ [$l ≡ set_; $a ≡ $b ⤳ $c.[]];
unif_rule @η $l $a ≡ Π x:τ $b, τ $c.[x] ↪ [$l ≡ set_; $a ≡ $b ⤳d λ x, $c.[x]];
