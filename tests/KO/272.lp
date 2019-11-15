constant symbol A : TYPE
constant symbol a : A
constant symbol B : A ⇒ TYPE
constant symbol C : A ⇒ TYPE

symbol f : A ⇒ A
symbol g : A ⇒ A

constant symbol consB : ∀a, B (g a)
constant symbol consC : ∀a, C (f a)

symbol calc :
  ∀ a : A,
  ∀ b : B a,
  ∀ c : C a,
  A

rule calc _ (consB _) (consC _) → A

rule f &x → &x
rule g &x → &x

rule calc _ (consB _) (consC _) → A
