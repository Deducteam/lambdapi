//set flag "print_implicits" on
//set verbose 3

// Type of set codes

constant symbol Set : TYPE

// Interpretation of set codes in TYPE

set declared "τ"

injective symbol τ : Set → TYPE

// Type of natural numbers

constant symbol nat : Set

definition N ≔ τ nat

constant symbol zero : N
constant symbol succ : N → N

// Type of polymorphic lists

constant symbol list : Set → Set

definition L a ≔ τ (list a)

set declared "□"

constant symbol □ {a} : L a
constant symbol cons {a} : τa → L a → L a

set infix 4 "⸬" ≔ cons

// Length of a list

symbol length {a} : L a → N

rule length □ ↪ zero
with length (_ ⸬ $l) ↪ succ (length $l)

// Concatenation of two lists

symbol concat {a} : L a → L a → L a

set infix right 5 "⋅" ≔ concat

rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m)
