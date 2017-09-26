type:Type.
o:type.
arrow: type ⇒ type ⇒ type.

term:type ⇒ Type.

App: a:type ⇒ b:type ⇒ term (arrow a b) ⇒ term a ⇒ term b.
Lam: a:type ⇒ b:type ⇒ (term a ⇒ term b) ⇒ term (arrow a b).

[f arg] App _ _ (Lam _ _ f) arg → f arg.

c:term o.

#EVAL App o o (Lam o o (λx:o.x)) c.
