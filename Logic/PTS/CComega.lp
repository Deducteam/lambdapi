/* Representation of the PTS underlying Agda, a predicative system
with an infinite hierarchy of sorts. */

require open Logic.PTS.Main;

constant symbol s : Set;
constant symbol a : F s → F s → Set;
constant symbol r : F s → F s → F s → Set;

// sorts are natural numbers
constant symbol zero : F s;
constant symbol succ : F s → F s;

// axioms
constant symbol α x : F (a x (succ x));

// max function on natural numbers
symbol ⊕ : F s → F s → F s;
notation ⊕ infix right 30;

rule zero ⊕ $y ↪ $y
with $x ⊕ zero ↪ $x
with succ $x ⊕ succ $y ↪ succ ($x ⊕ $y);

// rules
constant symbol ρ x y : F (r x y (x ⊕ y));
