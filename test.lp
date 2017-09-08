X : Type.
Y : Type.

#CHECK λx:X.x, x:X ⇒ X.
#CHECK λx:X.λy:Y.x, X ⇒ Y ⇒ X.

Nat  : Type.
zero : Nat.
succ : Nat ⇒ Nat.

Vec  : Nat ⇒ Type.
nil  : Vec zero.
cons : n:Nat ⇒ Nat ⇒ Vec n ⇒ Vec (succ n).

#INFER nil.
#INFER cons zero.
#INFER cons zero zero nil.

#CHECK nil, Vec zero.
#CHECK cons zero (succ zero) nil, Vec (succ zero).

add  : Nat ⇒ Nat ⇒ Nat.
[n]   add n        zero     → n.
[m]   add zero     m        → m.
[m n] add (succ n) m        → succ (add n m).
[m n] add n        (succ m) → succ (add n m).

#EVAL (λx:Nat.x) zero.
#EVAL add zero zero.
#EVAL add (succ (succ zero)) (succ zero).

id : (Nat ⇒ Nat) ⇒ Nat ⇒ Nat.
[n] id (λx:Nat.x) n → n.

#EVAL id (λy:Nat.y) (succ (succ zero)).
