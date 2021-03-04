// test matching on type annotations
symbol T:TYPE;
symbol a:T;
symbol b:T;
injective symbol U:T → TYPE;
symbol f:Π x:T,(U x → T) → T;
rule f _ (λ _:U a, a) ↪ b;
assert ⊢ f _ (λ _:U a, a) ≡ b;
assertnot ⊢ f _ (λ _:U b, a) ≡ b;
