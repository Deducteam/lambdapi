//flag "print_implicits" on
//verbose 3

// Type of set codes

constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE;

// Type of natural numbers

constant symbol nat : Set;

symbol N ≔ τ nat;

constant symbol zero : N;
constant symbol succ : N → N;

// Type of polymorphic lists

constant symbol list : Set → Set;

symbol L a ≔ τ (list a);

constant symbol □ [a] : L a;
constant symbol ⸬ [a] : τ a → L a → L a;

notation ⸬ infix right 4;

// Length of a list

symbol length [a] : L a → N;

rule length □ ↪ zero
with length (_ ⸬ $l) ↪ succ (length $l);

// Concatenation of two lists

symbol ⋅ [a] : L a → L a → L a;

notation ⋅ infix right 5;

rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m);
