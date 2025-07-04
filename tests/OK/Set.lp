// Type of set codes for quantifying over sets (polymorphism)

constant symbol Set : TYPE;

constant symbol ι : Set;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

builtin "T" ≔ τ;

// We assume that sets are non-empty

symbol el a : τ a;

// Cartesian product

constant symbol × : Set → Set → Set; notation × infix right 10; // \times

assert a b c ⊢ a × b × c ≡ a × (b × c);

symbol & [a b] : τ a → τ b → τ (a × b); notation & infix right 30;

assert a (x:τ a) b (y:τ b) c (z:τ c) ⊢ x & y & z : τ(a × b × c);
assert x y z ⊢ x & y & z ≡ x & (y & z);

symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;

rule ($x & _)₁ ↪ $x;

symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;

rule (_ & $x)₂ ↪ $x;
