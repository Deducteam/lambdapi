inductive nat : TYPE ≔
 | z    : nat
 | succ : nat → nat

// assert succ z : nat

inductive list ≔
 | nil  : list
 | cons : nat → list → list
