symbol A:TYPE;

symbol a:A;
symbol f:(A → A) → (A → A) → A;

rule f (λ x,$F.[x]) (λ y,$F.[y]) ↪ a;
assert ⊢ f (λ x,x) (λ y,y) ≡ a;

symbol g:(A → A → A) → (A → A) → A;

rule g (λ x y,$F.[x]) (λ x,$F.[x]) ↪ a;
assert ⊢ g (λ x y,x) (λ x,x) ≡ a;

symbol h:(A → A → A) → (A → A → A) → A;
symbol i: A → A → A;

rule h (λ x y,$F.[x,y]) (λ x y,$F.[y,x]) ↪ a;
assertnot ⊢ h (λ x y,i x y) (λ x y,i x y) ≡ a;
assert ⊢ h (λ x y,i x y) (λ x y,i y x) ≡ a;
