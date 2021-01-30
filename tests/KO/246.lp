constant symbol Type : TYPE;
injective symbol eta : Type → TYPE;

// function type
constant symbol Ar : Type → Type → Type;
set infix right 6 ">" ≔ Ar;
rule eta ($a > $b) ↪ eta $a → eta $b;

symbol fst : Π (A B : Type), eta (A > B > A) ≔
  λ A B a b, a;

symbol snd : Π (A B : Type), eta (A > B > B) ≔
  λ A B a b, a;
