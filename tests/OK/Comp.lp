/* Comparison datatype

By Quentin Garchery (May 2021). */

require open tests.OK.Bool;

inductive Comp : TYPE ≔
| Eq : Comp
| Lt : Comp
| Gt : Comp;

// set code for Comp

constant symbol comp : Set;

rule τ comp ↪ Comp;

// Boolean functions for testing head constructor

symbol isEq : Comp → 𝔹;

rule isEq Eq ↪ true
with isEq Lt ↪ false
with isEq Gt ↪ false;

symbol isLt : Comp → 𝔹;

rule isLt Eq ↪ false
with isLt Lt ↪ true
with isLt Gt ↪ false;

symbol isGt : Comp → 𝔹;

rule isGt Eq ↪ false
with isGt Lt ↪ false
with isGt Gt ↪ true;

symbol isLe : Comp → 𝔹;

rule isLe Eq ↪ true
with isLe Lt ↪ true
with isLe Gt ↪ false;

symbol isGe : Comp → 𝔹;

rule isGe Eq ↪ true
with isGe Lt ↪ false
with isGe Gt ↪ true;

// Discriminate constructors

opaque symbol Lt≠Eq : π (Lt ≠ Eq) ≔
begin
  assume h; refine ind_eq h (λ n, istrue(isEq n)) ⊤ᵢ
end;

opaque symbol Gt≠Eq : π (Gt ≠ Eq) ≔
begin
  assume h; refine ind_eq h (λ n, istrue(isEq n)) ⊤ᵢ
end;

opaque symbol Gt≠Lt : π (Gt ≠ Lt) ≔
begin
  assume h; refine ind_eq h (λ n, istrue(isLt n)) ⊤ᵢ
end;

// Opposite of a Comp

symbol opp : Comp → Comp;

rule opp Eq ↪ Eq
with opp Lt ↪ Gt
with opp Gt ↪ Lt;

opaque symbol opp_idem c : π (opp (opp c) = c) ≔
begin
  induction { reflexivity; } { reflexivity; } { reflexivity; }
end;

// Conditional

symbol case_Comp [A] : Comp → τ A → τ A → τ A → τ A;

rule case_Comp Eq $x _ _ ↪ $x
with case_Comp Lt _ $x _ ↪ $x
with case_Comp Gt _ _ $x ↪ $x;

// opp thms

opaque symbol isLt_opp c: π (isLt (opp c) = isGt c) ≔
begin
  induction {reflexivity}{reflexivity}{reflexivity};
end;

opaque symbol isGt_opp c: π (isGt (opp c) = isLt c) ≔
begin
  induction {reflexivity}{reflexivity}{reflexivity};
end;

opaque symbol isEq_opp c: π (isEq (opp c) = isEq c) ≔
begin
  induction {reflexivity}{reflexivity}{reflexivity};
end;
