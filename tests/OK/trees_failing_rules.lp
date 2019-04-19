symbol A : TYPE
symbol const N : TYPE
symbol zero : N
symbol succ : N ⇒ N
symbol pred : N ⇒ N

symbol f : A ⇒ A ⇒ A ⇒ A ⇒ A
symbol g : A ⇒ N ⇒ A

set builtin "0" ≔ zero
set builtin "+1" ≔ succ
set builtin "-1" ≔ pred

symbol a : A
symbol b : A
symbol c : A
symbol d : A
symbol e : A
symbol final : A
symbol init : A

rule f a b c d → f b c d a
and  f b d _ _ → e
and  f a c _ _ → e
and  f a d _ _ → e
and  f b a _ _ → e
and  f b c d a → f c d a b
and  f c d a b → f d a b c
and  f d a b c → final

rule g final (succ &n) → g init &n
 and g init &n → g (f a b c d) &n
 and g init zero → e

compute g init 10000