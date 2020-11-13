constant symbol A : TYPE;
constant symbol a : A;
constant symbol B : A → TYPE;
constant symbol C : A → TYPE;

symbol f : A → A;
symbol g : A → A;

constant symbol consB : Πa, B (g a);
constant symbol consC : Πa, C (f a);

symbol calc :
  Π a : A,
  Π b : B a,
  Π c : C a,
  A;

rule calc _ (consB _) (consC _) ↪ A;

rule f $x ↪ $x;
rule g $x ↪ $x;

rule calc _ (consB _) (consC _) ↪ A;
