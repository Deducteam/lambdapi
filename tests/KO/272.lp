symbol const A : TYPE
symbol const a : A
symbol const B : A ⇒ TYPE
symbol const C : A ⇒ TYPE

symbol f : A ⇒ A
symbol g : A ⇒ A

symbol const consB : ∀a, B (g a)
symbol const consC : ∀a, C (f a)

symbol calc :
  ∀ a : A,
  ∀ b : B a,
  ∀ c : C a,
  A

rule calc _ (consB _) (consC _) → A

rule f &x → &x
rule g &x → &x

rule calc _ (consB _) (consC _) → A
