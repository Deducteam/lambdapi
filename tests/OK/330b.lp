constant symbol Term : TYPE
constant symbol Prop : TYPE
symbol prf : Prop ⇒ TYPE
symbol prop_and : Prop ⇒ Prop ⇒ Prop
rule prf (prop_and &A &B) → ∀ C, (prf &A ⇒  prf &B ⇒  prf C) ⇒ prf C

definition and_elim_1 : ∀ A B, prf (prop_and A B) ⇒ prf A
≔  λ A B h, h A (λ a _, a)
