Nat : Type.
Z   : Nat.
S   : Nat ⇒ Nat.

def plus : Nat ⇒ Nat ⇒ Nat.
[x]   plus Z     x → x.
[x y] plus (S x) y → plus x (S y).

def mult : Nat ⇒ Nat ⇒ Nat.
[]    mult Z     _ → Z.
[x y] mult (S x) y → plus y (mult x y).

def fact : Nat ⇒ Nat.
[]  fact Z     → S Z.
[x] fact (S x) → mult (S x) (fact x).

def six   : Nat.
[] six   → (S (S (S (S (S (S Z)))))).

def seven : Nat.
[] seven → (S (S (S (S (S (S (S Z))))))).

def eight : Nat.
[] eight → (S (S (S (S (S (S (S (S Z)))))))).

def 0 : Nat.
def 1 : Nat.
def 2 : Nat.
def 3 : Nat.
def 4 : Nat.
def 5 : Nat.
def 6 : Nat.
def 7 : Nat.

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

#CONV (plus (fact 5) (fact 4)), (plus (fact 4) (fact 5)).
#CONV (plus (fact seven) (fact six)), (plus (fact six) (fact seven)).

// FIXME Takes too long? (dedukti: 116 seconds, here 300 seconds, factor 2.6)
//#CONV (plus (fact seven) (fact eight)), (plus (fact eight) (fact seven)).
