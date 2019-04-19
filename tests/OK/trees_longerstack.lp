symbol A : TYPE

symbol f : A ⇒ A ⇒ A

symbol a : A
symbol b : A

symbol g : A ⇒ A

rule g a → b
and g b → b

rule f a b → a
and  f a a → b

compute f (g a) a