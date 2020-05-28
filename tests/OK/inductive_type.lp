// Proposition type
constant symbol Prop : TYPE      // Type of propositions
set declared "π"
injective symbol π : Prop → TYPE // Interpretation of propositions in TYPE

set builtin "Prop"     ≔ Prop
set builtin "P"     ≔ π

constant symbol Set : TYPE       // Type of set codes
set declared "τ"
injective symbol τ : Set → TYPE  // Interpretation of set codes in TYPE

constant symbol eq {a} : τ a → τ a → Prop
set infix 8 "=" ≔ eq
constant symbol eq_refl {a} (x : τ a) : π (x = x)
constant symbol eq_ind {a} (x y : τ a) : π (x = y) → Πp, π (p y) → π (p x)

// Set builtins for the rewrite tactic
set builtin "T"     ≔ τ
set builtin "eq"    ≔ eq
set builtin "refl"  ≔ eq_refl
set builtin "eqind" ≔ eq_ind

constant symbol nat : Set
inductive Nat : TYPE ≔
 | z    : Nat
 | succ : Nat → Nat
//rule Nat ↪ τ nat
assert Nat_ind :
  Πp:Nat → Prop, π(p z) → (Πx, π (p x) → π (p (succ x))) → Πx, π (p x)

assert z : Nat
assert succ z : Nat
assert succ (succ (succ z)) : Nat

constant symbol list : Set
inductive List : TYPE ≔
 | nil  : List
 | cons : Nat → List → List

assert nil : List
assert cons (succ (succ (succ z))) nil : List
assert cons (succ (succ (succ z))) (cons (succ z) nil) : List
assert cons (succ (succ (succ z))) (cons (succ z) (cons z nil)) : List

set builtin "0"  ≔ z
set builtin "+1" ≔ succ

symbol plus : Nat → Nat → Nat
set infix left 6 "+" ≔ plus
assert λx y z,x+y+z ≡ λx y z,(x+y)+z // check that x+y=z is parsed correctly
rule       0 + $y ↪ $y
with succ $x + $y ↪ succ ($x + $y)

//theorem plus_0_n : Πn, π (eq {nat} (0 + n) n)
//proof
//qed
