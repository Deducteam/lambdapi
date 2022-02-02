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
with $x × s $y ↪ $x + $x × $y;

// Multiplication distributes over addition

opaque symbol mul_addl x y z : π ((x + y) × z = x × z + y × z) ≔
begin
induction
{ reflexivity }
{ assume x' h y z; simplify; rewrite h; reflexivity }
end;

rule ($x + $y) × $z ↪ $x × $z + $y × $z;

opaque symbol mul_addr x y z : π (z × (x + y) = z × x + z × y) ≔
begin
assume x y z; rewrite left mul_addl; reflexivity;
end;

rule $z × ($x + $y) ↪ $z × $x + $z × $y;

// Maximum

associative commutative symbol ∨: ℕ → ℕ → ℕ;

notation ∨ infix right 40;

rule 0 ∨ $x ↪ $x
with $x ∨ 0 ↪ $x
with s $x ∨ s $y ↪ s ($x ∨ $y);
