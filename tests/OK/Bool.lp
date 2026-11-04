// booleans

require open tests.OK.FOL tests.OK.Eq;

inductive 𝔹 : TYPE ≔ // `dB or \BbbB
| true : 𝔹
| false : 𝔹;

constant symbol bool : Set;

rule τ bool ↪ 𝔹;

// induction principle with equalities

opaque symbol case_𝔹 b : π (b = true ∨ b = false) ≔
begin
  induction
  { apply ∨ᵢ₁; reflexivity }
  { apply ∨ᵢ₂; reflexivity }
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

opaque symbol istrue=true [x] : π (istrue x) → π (x = true) ≔
begin
  assume x h;
  refine ∨ₑ (case_𝔹 x) _ _
      { assume h1; refine h1 }
      { assume h1;
      have H1: π (istrue false) { rewrite eq_sym h1; refine h };
      refine ⊥ₑ H1 };
end;

opaque symbol true=istrue [x] : π (x = true) → π (istrue x) ≔
begin
  assume x h;
  refine ∨ₑ (case_𝔹 x) _ _
      { assume h1; rewrite h1; refine ⊤ᵢ}
      { assume h1; rewrite h; refine ⊤ᵢ}
end;

opaque symbol ¬istrue=false [x : 𝔹]:
    π (¬ x) → π (x = false) ≔
begin
  assume x h;
  refine ∨ₑ (case_𝔹 x) _ _
      { assume h1; refine ⊥ₑ (h (true=istrue h1))}
      { assume h1; refine h1};
end;

opaque symbol false=¬istrue [x : 𝔹]:
    π (x = false) → π (¬ x) ≔
begin
  assume x h0; rewrite h0;
  assume h1; refine h1;
end;


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

opaque symbol ¬_istrue [p: 𝔹]:
    π(¬ p) → π(not p) ≔
begin
  induction
  { simplify; assume h; refine h ⊤ᵢ }
  { simplify; assume h; refine ⊤ᵢ }
end;

opaque symbol istrue_not [p: 𝔹]:
    π(not p) → π(¬ p)≔
begin
  induction
  { simplify; assume h0 h1; refine h0 }
  { simplify; assume h0 h1; refine h1 }
end;

opaque symbol notK b : π (not (not b) = b) ≔
begin
  induction
  { reflexivity }
  { reflexivity }
end;

opaque symbol not_inj [b c] : π (not b = not c) → π (b = c) ≔
begin
  induction
  { induction
    { reflexivity }
    { assume h; apply ⊥ₑ (false≠true h) }
  }
  { induction
    { assume h; apply ⊥ₑ (true≠false h) }
    { reflexivity }
  }
end;

// or

symbol or : 𝔹 → 𝔹 → 𝔹;

notation or infix left 20;

rule true  or _     ↪ true
with false or $b    ↪ $b;

opaque symbol or_true b: π(b or true = true) ≔
begin induction {reflexivity} {reflexivity} end;

opaque symbol or_false b: π(b or false = b) ≔
begin induction {reflexivity} {reflexivity} end;

// imp

symbol imp (b c : 𝔹) : 𝔹 ≔ not b or c;

notation imp infix left 20;

opaque symbol ⇒_istrue [p q : 𝔹] : π(p imp q) → π(p ⇒ q) ≔
begin
  induction
  { induction
    { assume h1; refine (λ x, x) }
    { assume h1 h2; refine h1 }
  }
  {
    induction
    { assume h1 h2; apply h1 }
    { assume h1; refine (λ x, x) }
   }
end;

opaque symbol istrue_imp [p q : 𝔹] : π(p ⇒ q) → π(p imp q) ≔
begin
  induction
  { induction
    { assume h; apply ⊤ᵢ }
    { assume h; apply h ⊤ᵢ }
  }
  { induction
    { assume h; apply ⊤ᵢ }
    { assume h; apply ⊤ᵢ }
  }
end;

opaque symbol impᵢ [p q : 𝔹] : (π p → π q) → π (p imp q) ≔
begin
  assume p q h; apply @istrue_imp p q h;
end;

opaque symbol impₑ [p q : 𝔹] : π (p imp q) → π p → π q ≔
begin
  assume p q h; refine @⇒_istrue p q h;
end;

opaque symbol ∨_istrue [p q : 𝔹] : π(p or q) → π(p ∨ q) ≔
begin
  induction
  { assume q h; apply ∨ᵢ₁; apply ⊤ᵢ }
  { assume q h; apply ∨ᵢ₂; apply h }
end;

opaque symbol istrue_or [p q : 𝔹] : π(p ∨ q) → π(p or q) ≔
begin
  induction
  { assume q h; apply ⊤ᵢ }
  { assume q h; apply ∨ₑ h { assume i; apply ⊥ₑ i } { assume i; apply i } }
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
    { assume q; rewrite or_true; reflexivity }
    { assume q; rewrite or_false; reflexivity }
end;

opaque symbol orA p q r : π ((p or q) or r = p or (q or r)) ≔
begin
    induction
    { reflexivity }
    { reflexivity }
end;

// and

symbol and : 𝔹 → 𝔹 → 𝔹;

notation and infix left 15;

rule true  and $b    ↪ $b
with false and _     ↪ false;

opaque symbol and_true b: π(b and true = b) ≔
begin induction {reflexivity} {reflexivity} end;

opaque symbol and_false b: π(b and false = false) ≔
begin induction {reflexivity} {reflexivity} end;

opaque symbol ∧_istrue [p q : 𝔹] : π(p and q) → π(p ∧ q) ≔
begin
  induction
  { induction
    { assume h; apply ∧ᵢ { apply ⊤ᵢ } { apply ⊤ᵢ } }
    { assume h; apply ⊥ₑ h }
  }
  { assume q h; apply ⊥ₑ h }
end;

opaque symbol istrue_and [p q : 𝔹] : π(p ∧ q) → π(p and q) ≔
begin
  induction
  { assume q h; apply ∧ₑ₂ h }
  { assume q h; apply ∧ₑ₁ h }
end;

opaque symbol andᵢ [p q : 𝔹] : π p → π q → π(p and q) ≔
begin
  assume p q h i; apply @istrue_and p q; apply ∧ᵢ h i;
end;

opaque symbol andₑ₁ [p q : 𝔹] : π (p and q) → π p ≔
begin
  induction
  { assume q i; apply ⊤ᵢ }
  { assume q i; apply i }
end;

opaque symbol andₑ₂ [p q : 𝔹] : π (p and q) → π q ≔
begin
  induction
  { assume q i; apply i }
  { assume q i; apply ⊥ₑ i }
end;

// xorb

symbol xorb : 𝔹 → 𝔹 → 𝔹;

notation xorb infix left 22;

rule false xorb $b ↪ $b
with true xorb $b ↪ not $b;

opaque symbol xorbᵢ₁ [p q : 𝔹] : π p → π (not q) → π (p xorb q) ≔
begin
  induction
  { assume q h i; apply i }
  { assume q h i; apply ⊥ₑ h }
end;

opaque symbol xorbᵢ₂ [p q : 𝔹] : π (not p) → π q → π (p xorb q) ≔
begin
  induction
  { assume q h i; apply ⊥ₑ h }
  { assume q h i; apply i }
end;

opaque symbol xorbₑ [p q : 𝔹] (r : 𝔹) :
  π (p xorb q) → (π p → π (not q) → π r) → (π (not p) → π q → π r) → π r ≔
begin
  induction
  { assume q r h h1 h2; apply h1 ⊤ᵢ h }
  { assume q r h h1 h2; apply h2 ⊤ᵢ h }
end;

// if-then-else

symbol if : 𝔹 → Π [a], τ a → τ a → τ a;

rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;

opaque symbol if_true [a] (x y : τ a) : π (if true x y = x) ≔
begin reflexivity end;

opaque symbol if_false [a] (x y : τ a) : π (if false x y = y) ≔
begin reflexivity end;

opaque symbol if_same b [a] (x : τ a) : π (if b x x = x) ≔
begin
  assume b a x;
  refine ∨ₑ (case_𝔹 b) _ _
    { assume h; rewrite h; reflexivity }
    { assume h; rewrite h; reflexivity }
end;

opaque symbol if_id b : π (if b true false = b) ≔
begin
  induction
  { reflexivity }
  { reflexivity }
end;

opaque symbol if_not b [a] (x y : τ a) : π (if (not b) x y = if b y x) ≔
begin
  assume b a x y;
  refine ∨ₑ (case_𝔹 b) _ _
    { assume h; rewrite h; reflexivity }
    { assume h; rewrite h; reflexivity }
end;

opaque symbol if_istrue [b : 𝔹] [a] (x y : τ a) : π b → π (if b x y = x) ≔
begin
  assume b a x y h;
  refine ∨ₑ (case_𝔹 b) _ _
    { assume h1; rewrite h1; reflexivity }
    { assume h1; apply ⊥ₑ (false=¬istrue h1 h) }
end;

opaque symbol if_isfalse [b : 𝔹] [a] (x y : τ a) : π (not b) → π (if b x y = y) ≔
begin
  assume b a x y h;
  refine ∨ₑ (case_𝔹 b) _ _
    { assume h1; apply ⊥ₑ (istrue_not h (true=istrue h1)) }
    { assume h1; rewrite h1; reflexivity }
end;

