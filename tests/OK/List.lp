require open tests.OK.Set tests.OK.Prop tests.OK.Eq tests.OK.Nat tests.OK.Bool;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a // \Box
| ⸬ : τ a → 𝕃 a → 𝕃 a; // ::

notation ⸬ infix right 20;

// set code for 𝕃

constant symbol list : Set → Set;

rule τ (list $a) ↪ 𝕃 $a;

symbol size [a] : 𝕃 a → ℕ;

rule size □ ↪ 0;

type size (0 ⸬ □);

symbol + : ℕ → ℕ → ℕ; notation + infix right 10;

symbol - : ℕ → ℕ; notation - prefix 20;

debug +o;

type 0 + 0;

type - - 0;

type 0 +1;

type (size □) +1;

rule size (_ ⸬ $l) ↪ (size $l) +1;
