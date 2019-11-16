symbol const A : TYPE
symbol const a : A
symbol f : (A ⇒ A) ⇒ A
rule f (λ x, &X &Y) → a
 and f (&X &Y) → a
symbol x : A ⇒ A
symbol y : A
compute f (λ z, (x y))
