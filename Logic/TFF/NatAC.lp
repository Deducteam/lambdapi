// Natural numbers

require open Logic.TFF.Set Logic.TFF.Prop Logic.TFF.Main Logic.TFF.Eq
             Logic.TFF.Nat;

// Addition

associative commutative symbol + : ℕ → ℕ → ℕ;

notation + infix right 20;

rule 0 + $x ↪ $x
with $x + 0 ↪ $x
with s $x + $y ↪ s ($x + $y)
with $x + s $y ↪ s ($x + $y);

// Multiplication

associative commutative symbol × : ℕ → ℕ → ℕ; // \times

notation × infix right 30;

rule 0 × _  ↪ 0
with _ × 0 ↪ 0
with s $x × $y ↪ $y + $x × $y
with $x × s $y ↪ $x + $x × $y
with ($x + $y) × $z ↪ $x × $z + $y × $z
with $z × ($x + $y) ↪ $z × $x + $z × $y;

/* Check the confluence of critical pairs unjoianble in Nat. */
assert v0 v1 v2 v1' v2' ⊢
  (s v0 × v1') + (s v0 × v2') ≡ (v1' + v2') + (v0 × (v1' + v2'));
assert v0 v1' ⊢ s v0 + (s v0 × v1') ≡ s v1' + (v0 × s v1');
assert v0 v2' v1 ⊢ (v0 × v2') + (s v1 × v2') ≡ s (v0 + v1) × v2';
assert v0 v1 v2' ⊢ s v0 × (v1 × v2') ≡ (v1 + (v0 × v1)) × v2';

// Maximum

associative commutative symbol ∨: ℕ → ℕ → ℕ; // || or \vee

notation ∨ infix right 40;

rule 0 ∨ $x ↪ $x
with $x ∨ 0 ↪ $x
with s $x ∨ s $y ↪ s ($x ∨ $y);
