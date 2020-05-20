inductive nat : TYPE ≔
 | z    : nat
 | succ : nat → nat

assert z : nat
assert succ z : nat
assert succ (succ (succ z)) : nat

//assert nat_ind : TYPE
//"π" (p 0) → (Πx, π (p x) → π (p (succ x))) → Πx, π (p x)

inductive list : TYPE ≔
 | nil  : list
 | cons : nat → list → list

assert nil : list
assert cons (succ (succ (succ z))) nil : list
assert cons (succ (succ (succ z))) (cons (succ z) nil) : list
assert cons (succ (succ (succ z))) (cons (succ z) (cons z nil)) : list
