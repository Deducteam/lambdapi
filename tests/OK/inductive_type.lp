// Proposition type
constant symbol Prop : TYPE      // Type of propositions
set declared "π"
injective symbol π : Prop → TYPE // Interpretation of propositions in TYPE

set builtin "Prop"     ≔ Prop
set builtin "P"     ≔ π

inductive nat : TYPE ≔
 | z    : nat
 | succ : nat → nat

assert z : nat
assert succ z : nat
assert succ (succ (succ z)) : nat

inductive list : TYPE ≔
 | nil  : list
 | cons : nat → list → list

assert nil : list
assert cons (succ (succ (succ z))) nil : list
assert cons (succ (succ (succ z))) (cons (succ z) nil) : list
assert cons (succ (succ (succ z))) (cons (succ z) (cons z nil)) : list
