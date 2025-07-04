/* Comparison datatype

By Quentin Garchery (May 2021). */

require open tests.OK.Set tests.OK.Prop tests.OK.FOL tests.OK.Eq
  tests.OK.Bool;

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

rule isLt Eq ↪ true
with isLt Lt ↪ true
with isLt Gt ↪ false;

symbol isGe : Comp → 𝔹;

rule isLt Eq ↪ true
with isLt Lt ↪ false
with isLt Gt ↪ true;

// Discriminate constructors

symbol Lt≠Eq : π (Lt ≠ Eq) ≔
begin
  assume h; refine ind_eq h (λ n, istrue(isEq n)) ⊤ᵢ
end;

symbol Gt≠Eq : π (Gt ≠ Eq) ≔
begin
  assume h; refine ind_eq h (λ n, istrue(isEq n)) ⊤ᵢ
end;

symbol Gt≠Lt : π (Gt ≠ Lt) ≔
begin
  assume h; refine ind_eq h (λ n, istrue(isLt n)) ⊤ᵢ
end;

// Opposite of a Comp

symbol opp : Comp → Comp;

rule opp Eq ↪ Eq
with opp Lt ↪ Gt
with opp Gt ↪ Lt;

symbol opp_idem c : π (opp (opp c) = c) ≔
begin
  induction { reflexivity; } { reflexivity; } { reflexivity; }
end;

// Conditional

symbol case_Comp [A] : Comp → τ A → τ A → τ A → τ A;

rule case_Comp Eq $x _ _ ↪ $x
with case_Comp Lt _ $x _ ↪ $x
with case_Comp Gt _ _ $x ↪ $x;
