// Cartesian product

require open tests.OK.Set;

constant symbol × : Set → Set → Set; notation × infix right 10; // \times

assert a b c ⊢ a × b × c ≡ a × (b × c);

symbol ‚ [a b] : τ a → τ b → τ (a × b); notation ‚ infix right 30;

assert a (x:τ a) b (y:τ b) c (z:τ c) ⊢ x ‚ y ‚ z : τ(a × b × c);
assert x y z ⊢ x ‚ y ‚ z ≡ x ‚ (y ‚ z);

symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;

rule ($x ‚ _)₁ ↪ $x;

symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;

rule (_ ‚ $x)₂ ↪ $x;
