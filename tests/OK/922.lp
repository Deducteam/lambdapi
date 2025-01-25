require open tests.OK.Set tests.OK.Prop tests.OK.Eq tests.OK.Bool;

inductive ℕ : TYPE ≔
| O : ℕ
| +1 : ℕ → ℕ;

constant symbol nat : Set;

rule τ nat ↪ ℕ;

notation +1 postfix 10;

symbol isO : ℕ → 𝔹;

rule isO O ↪ true
with isO (_ +1) ↪ false;

opaque symbol s≠O [n] : π (n +1 ≠ O) ≔
begin
  assume n h; refine ind_eq h (λ n, istrue(isO n)) ⊤ᵢ
end;
