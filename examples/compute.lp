Nat : Type.
Z   : Nat.
S   : Nat ⇒ Nat.

plus : Nat ⇒ Nat ⇒ Nat.
[x]   plus Z     x → x.
[x y] plus (S x) y → plus x (S y).

mult : Nat ⇒ Nat ⇒ Nat.
[]    mult Z _     → Z.
[x y] mult (S x) y → plus y (mult x y).

fact : Nat ⇒ Nat.
[]  fact Z     → S Z.
[x] fact (S x) → mult (S x) (fact x).

six   : Nat.
[] six   → (S (S (S (S (S (S Z)))))).

seven : Nat.
[] seven → (S (S (S (S (S (S (S Z))))))).

// FIXME
// #CONV	(plus (fact seven) (fact six)),	(plus (fact six) (fact seven)).
