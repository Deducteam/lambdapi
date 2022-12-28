require open tests.OK.Set tests.OK.Prop tests.OK.Eq tests.OK.Bool;

inductive ℕ : TYPE ≔
| 0 : ℕ
| +1 : ℕ → ℕ;

constant symbol nat : Set;

rule τ nat ↪ ℕ;

notation +1 postfix 10;

builtin "0"  ≔ 0;
builtin "+1" ≔ +1;

symbol is0 : ℕ → 𝔹;

rule is0 0 ↪ true
with is0 (_ +1) ↪ false;

opaque symbol s≠0 [n] : π (n +1 ≠ 0) ≔
begin
  assume n h; refine ind_eq h (λ n, istrue(is0 n)) top
end;
