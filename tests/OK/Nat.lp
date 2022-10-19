require open tests.OK.Set tests.OK.Prop tests.OK.Eq tests.OK.Bool;

inductive ℕ : TYPE ≔
| 0 : ℕ
| +1 : ℕ → ℕ; notation +1 postfix 100;

builtin "0"  ≔ 0;
builtin "+1" ≔ +1;

constant symbol nat : Set;

rule τ nat ↪ ℕ;
