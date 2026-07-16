require open tests.OK.Set tests.OK.Prop;

constant symbol L:TYPE;
constant symbol prop:L;
constant symbol set_:L;

injective symbol U:L → TYPE;
rule U prop ↪ Prop
with U set_ ↪ Set;

symbol ϵ:Π [l:L], U l → TYPE;
rule ϵ [prop] $a ↪ π $a
with ϵ [set_] $a ↪ τ $a;

unif_rule ϵ $a ≡ π $b ↪ [$a ≡ $b];
unif_rule ϵ $a ≡ τ $b ↪ [$a ≡ $b];

require private open tests.OK.Tactic;

private symbol tac: Π [l:L], Π [a:U l], ϵ a → Tactic;

type λ a:Set, λ x:τ a, tac x;
