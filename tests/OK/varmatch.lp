symbol const A : TYPE

symbol const id : A ⇒ A
symbol f : (A ⇒ A) ⇒ (A ⇒ A)
rule f (λ x, x) → id

assert f (λ x, x) ≡ id