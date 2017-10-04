Nat : Type.

0 : Nat.
S : Nat ⇒ Nat.

Elt : Type.

Vec : Nat ⇒ Type.

nil : Vec 0.
cns : n:Nat ⇒ Elt ⇒ Vec n ⇒ Vec (S n).

tail : n:Nat ⇒ Vec (S n) ⇒ Vec n.
[n l] tail n (cns n _ l) → l.
