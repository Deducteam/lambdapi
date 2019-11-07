set flag "eta_equality" on

symbol const Type : TYPE
symbol const f : Type ⇒ Type
symbol const g : (Type ⇒ Type) ⇒ Type
assert g (λ x, f x) ≡ g f
assert (λ x, f x) ≡ f
assert f ≡ (λ x, f x)
