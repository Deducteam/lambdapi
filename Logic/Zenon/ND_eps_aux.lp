// auxiliary meta-theorems of first-order logic

require open Logic.Zenon.FOL Logic.Zenon.ND Logic.Zenon.ND_eps;

symbol nnpp p : ϵ (¬ ¬ p) → ϵ p;

opaque symbol Lcontraposition p q
: ϵ (p ⇒ q) → ϵ ((¬ q) ⇒ (¬ p))
≔ λ h1 h2 h3, h2 (h1 h3);

opaque symbol L⇔1 p q
: (ϵ q → ϵ p) → (ϵ p → ϵ (¬ q)) → ϵ q → ϵ (¬ q)
≔ λ h5 h2 hq, h2 (h5 hq);

opaque symbol L⇔2 p q
: (ϵ q → ϵ p) → (ϵ p → ϵ (¬ q)) → ϵ (¬ q)
≔ λ h5 h2 hq, L⇔1 p q h5 h2 hq hq;

opaque symbol L⇔3 p q
: (ϵ q → ϵ p) → (ϵ p → ϵ (¬ q)) → (ϵ p → ϵ q) → ϵ (¬ p)
≔ λ h5 h2 h4, Lcontraposition p q h4 (L⇔2 p q h5 h2);

opaque symbol L⇔4 p q
: (ϵ q → ϵ p) → (ϵ p → ϵ (¬ q)) → (ϵ p → ϵ q)
  → (ϵ (¬ p) → ϵ (¬ ¬ q)) → ϵ (¬ ¬ q)
≔ λ h5 h2 h4 h1, h1 (L⇔3 p q h5 h2 h4);

opaque symbol L¬∨1 p q : ϵ p → ϵ (p ∨ q) ≔ @∨Il p q;

opaque symbol L¬∨2 p q : ϵ q → ϵ (p ∨ q) ≔ @∨Ir p q;

opaque symbol L¬∨3 p q : ϵ (¬ (p ∨ q)) → ϵ (¬ p)
≔ λ h2, Lcontraposition p (p ∨ q) (L¬∨1 p q) h2;

opaque symbol L¬∨4 p q : ϵ (¬ (p ∨ q)) → ϵ (¬ q)
≔ λ h2, Lcontraposition q (p ∨ q) (L¬∨2 p q) h2;

opaque symbol L¬⇒1 p q : ϵ (¬ (p ⇒ q)) → ϵ (¬ q)
≔ λ h2 h3, h2 (λ _, h3);

opaque symbol L¬⇒2 p q
: (ϵ p → ϵ (¬ ¬ q)) → ϵ (¬ (p ⇒ q)) → ϵ (¬ p)
≔ λ h1 h2 h3, h1 h3 (L¬⇒1 p q h2);
 
opaque symbol L¬⇒3 p q : ϵ (¬ p) → ϵ (p ⇒ q)
≔ λ h3 h4, ⊥E (h3 h4) q;

opaque symbol L¬⇔1 p q
: (ϵ p → ϵ (¬ ¬ q)) → ϵ (¬ (p ⇔ q)) → ϵ (¬ p) ≔ λ h2 h3 hp,
h2 hp (λ hq, h3 (@∧I (p ⇒ q) (q ⇒ p) (λ _, hq) (λ _, hp)));
