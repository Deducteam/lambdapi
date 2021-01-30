set flag "eta_equality" on;

constant symbol Type : TYPE;
constant symbol f : Type → Type;
constant symbol g : (Type → Type) → Type;
assert ⊢ g (λ x, f x) ≡ g f;
assert ⊢ (λ x, f x) ≡ f;
assert ⊢ f ≡ (λ x, f x);
