constant symbol A : TYPE;

constant symbol f : A → A;

constant symbol B : A → TYPE;
constant symbol consB : Π x, B (f x);

constant symbol C : A → A → TYPE;
constant symbol consC : Π x, C x (f x);

symbol k : Π a, B a → A;
rule k _ (consB $b) ↪ $b;

symbol calc : Π a b, C (f a) (k a b) → TYPE;

constant symbol D : Π x, B (f (f x)) → TYPE;

rule calc $a (consB $b) (consC _) ↪ D $b (consB $a);
