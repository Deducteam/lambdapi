symbol A : TYPE

symbol a : A
symbol b : A

symbol f : A ⇒ A

rule f a → b
compute f a

symbol g : A ⇒ A
rule g b → a

compute g (f a)

symbol h : A ⇒ A ⇒ A
rule h a a → h (f a) b
and h b b → b
and h a b → g b

compute h (g (f a))