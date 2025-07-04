/* Library on booleans. */

require open tests.OK.Set tests.OK.Prop tests.OK.FOL tests.OK.Eq;

inductive 𝔹 : TYPE ≔ // `dB or \BbbB
| true : 𝔹
| false : 𝔹;

constant symbol bool : Set;

rule τ bool ↪ 𝔹;

// induction principle with equalities

opaque symbol case_𝔹 b : π (b = true ∨ b = false) ≔
begin
  induction
  { apply ∨ᵢ₁; reflexivity; }
  { apply ∨ᵢ₂; reflexivity; }
end;

opaque symbol ind_𝔹_eq p b:
 (π(b = true) → π(p b)) → (π(b = false) → π(p b)) → π(p b) ≔
begin
  assume p b t f; refine ∨ₑ (case_𝔹 b) t f;
end;

// istrue predicate

injective symbol istrue : 𝔹 → Prop;

rule istrue true ↪ ⊤
with istrue false ↪ ⊥;

coerce_rule coerce 𝔹 Prop $x ↪ istrue $x;

// non confusion of constructors

opaque symbol false≠true : π (false ≠ true) ≔
begin
  assume h; refine ind_eq h istrue ⊤ᵢ
end;

opaque symbol true≠false : π (true ≠ false) ≔
begin
  assume h; apply false≠true; symmetry; apply h
end;

// not

symbol not : 𝔹 → 𝔹;

rule not true  ↪ false
with not false ↪ true;

// or

symbol or : 𝔹 → 𝔹 → 𝔹;

notation or infix left 20;

rule true  or _     ↪ true
with _     or true  ↪ true
with false or $b    ↪ $b
with $b    or false ↪ $b;

opaque symbol ∨_istrue [p q : 𝔹] : π(p or q) → π(p ∨ q) ≔
begin
  induction
  { assume q h; apply ∨ᵢ₁; apply ⊤ᵢ; }
  { assume q h; apply ∨ᵢ₂; apply h; }
end;

opaque symbol istrue_or [p q : 𝔹] : π(p ∨ q) → π(p or q) ≔
begin
  induction
  { assume q h; apply ⊤ᵢ; }
  { assume q h; apply ∨ₑ h { assume i; apply ⊥ₑ i; } { assume i; apply i; } }
end;

opaque symbol orᵢ₁ [p : 𝔹] q : π p → π (p or q) ≔
begin
  induction
  { simplify; assume b h; apply ⊤ᵢ }
  { simplify; assume b h; apply ⊥ₑ h }
end;

opaque symbol orᵢ₂ p [q : 𝔹] : π q → π (p or q) ≔
begin
  induction
  { simplify; assume b h; apply ⊤ᵢ }
  { simplify; assume b h; apply h }
end;

opaque symbol orₑ [p q : 𝔹] (r : 𝔹) :
  π (p or q) → (π p → π r) → (π q → π r) → π r ≔
begin
  assume p q r pq pr qr;
  have h: π(p ∨ q) { apply ∨_istrue pq };
  apply ∨ₑ h pr qr;
end;

opaque symbol orC p q : π (p or q = q or p) ≔
begin
    induction
    { reflexivity; }
    { reflexivity; }
end;

opaque symbol orA p q r : π ((p or q) or r = p or (q or r)) ≔
begin
    induction
    { reflexivity; }
    { reflexivity; }
end;

// and

symbol and : 𝔹 → 𝔹 → 𝔹;

notation and infix left 7;

rule true  and $b    ↪ $b
with $b    and true  ↪ $b
with false and _     ↪ false
with _     and false ↪ false;

opaque symbol ∧_istrue [p q : 𝔹] : π(p and q) → π(p ∧ q) ≔
begin
  induction
  { induction
    { assume h; apply ∧ᵢ { apply ⊤ᵢ } { apply ⊤ᵢ } }
    { assume h; apply ⊥ₑ h; }
  }
  { assume q h; apply ⊥ₑ h; }
end;

opaque symbol istrue_and [p q : 𝔹] : π(p ∧ q) → π(p and q) ≔
begin
  induction
  { assume q h; apply ∧ₑ₂ h; }
  { assume q h; apply ∧ₑ₁ h; }
end;

opaque symbol andᵢ [p q : 𝔹] : π p → π q → π(p and q) ≔
begin
  assume p q h i; apply @istrue_and p q; apply ∧ᵢ h i;
end;

opaque symbol andₑ₁ [p q : 𝔹] : π (p and q) → π p ≔
begin
  induction
  { assume q i; apply ⊤ᵢ; }
  { assume q i; apply i; }
end;

opaque symbol andₑ₂ [p q : 𝔹] : π (p and q) → π q ≔
begin
  induction
  { assume q i; apply i; }
  { assume q i; apply ⊥ₑ i; }
end;

// if-then-else

symbol if : 𝔹 → Π [a], τ a → τ a → τ a;

rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;
