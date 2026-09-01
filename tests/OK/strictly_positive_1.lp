// test generation of inductive principle for a strictly-positive type
// with a constructor taking a binary function as argument

constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE;
builtin "Prf" ≔ π;

constant symbol ℕ:TYPE;

inductive 𝕆:TYPE ≔ z:𝕆 | s:𝕆 → 𝕆 | l:(ℕ → ℕ → 𝕆) → 𝕆;

assert ⊢ 𝕆:TYPE;
assert ⊢ z:𝕆;
assert ⊢ s:𝕆 → 𝕆;
assert ⊢ l:(ℕ → ℕ → 𝕆) → 𝕆;

assert ⊢ ind_𝕆: Π p, π (p z) → (Π x, π (p x) → π (p (s x)))
  → (Π x, (Π y z, π (p (x y z))) → π (p (l x))) → Π x, π (p x);

assert p a b c ⊢ ind_𝕆 p a b c z ≡ a;
assert p a b c x ⊢ ind_𝕆 p a b c (s x) ≡ b x (ind_𝕆 p a b c x);
assert p a b c x y ⊢ ind_𝕆 p a b c (l x) ≡ c x (λ y z, ind_𝕆 p a b c (x y z));
