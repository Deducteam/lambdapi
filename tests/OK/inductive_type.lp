inductive nat : TYPE ≔
 | z    : nat
 | succ : nat → nat

inductive list ≔
 | nil  : list
 | cons : nat → list → list
