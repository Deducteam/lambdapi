Nat : Type.

0 : Nat.
S : Nat ⇒ Nat.

def half : Nat ⇒ Nat.

[]  half 0         → 0.
[]  half (S 0)     → 0.
[n] half (S (S n)) → half n.

#CONV half 0, half (S 0).
