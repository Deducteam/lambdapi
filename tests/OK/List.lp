require open tests.OK.Set tests.OK.Prop tests.OK.Eq tests.OK.Nat tests.OK.Bool;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a // \Box
| ⸬ : τ a → 𝕃 a → 𝕃 a; // ::

notation ⸬ infix right 20;

// set code for 𝕃

constant symbol list : Set → Set;

rule τ (list $a) ↪ 𝕃 $a;

symbol size [a] : 𝕃 a → ℕ;

debug +o;
rule size □ ↪ 0
with size (_ ⸬ $l) ↪ (size $l) +1;
