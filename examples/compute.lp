Nat : Type.
Z   : Nat.
S   : Nat ⇒ Nat.

plus : Nat ⇒ Nat ⇒ Nat.
[x]   plus Z     x → x.
[x y] plus (S x) y → plus x (S y).

mult : Nat ⇒ Nat ⇒ Nat.
[]    mult Z     _ → Z.
[x y] mult (S x) y → plus y (mult x y).

fact : Nat ⇒ Nat.
[]  fact Z     → S Z.
[x] fact (S x) → mult (S x) (fact x).

six   : Nat.
[] six   → (S (S (S (S (S (S Z)))))).

seven : Nat.
[] seven → (S (S (S (S (S (S (S Z))))))).

0 : Nat.
1 : Nat.
2 : Nat.
3 : Nat.
4 : Nat.
5 : Nat.
6 : Nat.
7 : Nat.

[] 0 → Z.
[] 1 → S 0.
[] 2 → S 1.
[] 3 → S 2.
[] 4 → S 3.
[] 5 → S 4.
[] 6 → S 5.
[] 7 → S 6.

#EVAL 0.
#EVAL 1.
#EVAL 2.
#EVAL 3.
#EVAL 4.
#EVAL 5.
#EVAL 6.
#EVAL 7.

#EVAL (fact 0).
#EVAL (fact 1).
#EVAL (fact 2).
#EVAL (fact 3).

#EVAL (plus (fact 3) (fact 2)).
#EVAL (plus (fact 2) (fact 3)).

// Takes too long ?
//#CONV (plus (fact seven) (fact six)), (plus (fact six) (fact seven)).
#CONV (plus (fact 5) (fact 4)), (plus (fact 4) (fact 5)).

