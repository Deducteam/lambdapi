symbol const A : TYPE

symbol f : A ⇒ A ⇒ A

symbol a : A
symbol b : A

symbol g : A ⇒ A
symbol h : A ⇒ A ⇒ A


rule f a &x → h &x &x
and f &y &x → h &x &y

symbol i : A ⇒ A ⇒ A
compute f (g b) a
compute f (g b) (g a)