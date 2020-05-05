inductive nat : TYPE ≔
 | z    : nat
 | succ : nat → nat

inductive list ≔
 | nil  : list
 | cons : a → list → list

symbol nat : TYPE

definition test (x:nat) ≔ x
