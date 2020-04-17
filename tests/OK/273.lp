constant symbol A : TYPE

constant symbol f : A → A

constant symbol B : A → TYPE
constant symbol consB : Πx, B (f x)

constant symbol C : A → A → TYPE
constant symbol consC : Πx, C x (f x)

symbol k : Πa, B a → A
rule k _ (consB $b) ↪ $b

symbol calc : Πa b, C (f a) (k a b) → TYPE

constant symbol D : Πx, B (f (f x)) → TYPE

rule calc $a (consB $b) (consC _) ↪ D $b (consB $a)
