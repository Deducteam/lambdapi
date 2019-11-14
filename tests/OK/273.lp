symbol const A : TYPE

symbol const f : A ⇒ A

symbol const B : A ⇒ TYPE
symbol const consB : ∀x, B (f x)

symbol const C : A ⇒ A ⇒ TYPE
symbol const consC : ∀x, C x (f x)

symbol k : ∀a, B a ⇒ A
rule k _ (consB &b) → &b

symbol calc : ∀a b, ∀c : C (f a) (k a b), TYPE

symbol const D : ∀x, B (f (f x)) ⇒ TYPE

rule calc &a (consB &b) (consC _) → D &b (consB &a)
