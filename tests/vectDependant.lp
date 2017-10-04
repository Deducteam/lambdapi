Nat : Type.

0 : Nat.
S : Nat ⇒ Nat.

1 : Nat.
2 : Nat.
3 : Nat.
4 : Nat.

[] 1 → S 0.
[] 2 → S 1.
[] 3 → S 2.
[] 4 → S 3.

Vec : Nat ⇒ Type.

nil : Vec 0.
cns : n : Nat ⇒ Vec n ⇒ Vec (S n).

tail : n:Nat ⇒ Vec (S n) ⇒ Vec n.
[n l] tail n (cns _ l) → l.

S_bis : Nat ⇒ Nat.
[]  S_bis 0         → S (S 0).
[]  S_bis (S 0)     → S (S 0).
[n] S_bis (S (S n)) → S (S (S_bis n)).

cns_bis : n:Nat ⇒ Vec n ⇒ Vec (S_bis n).

tail_bis : n:Nat ⇒ Vec (S_bis n) ⇒ Vec n.
[n l] tail_bis n (cns_bis _ l) → l.

left  : Vec 3.
[] left  → cns 2 (cns 1 (cns 0 nil)).

right : Vec 2.
[] right → tail_bis 2 (cns_bis 3 left).

#EVAL left.
#EVAL right.
#CONV left, right.
// FIXME two convertible terms with different types...
