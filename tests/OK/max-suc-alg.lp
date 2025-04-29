// universe levels as in Agda syntax
constant symbol L : TYPE;
symbol Z : L;
symbol S : L → L;
symbol ∪ : L → L → L; notation ∪ infix right 10;
symbol V : L → L; // to mark universe level variables

// natural numbers
constant symbol ℕ : TYPE;
constant symbol Oₙ : ℕ;
constant symbol sₙ : ℕ → ℕ;

// max function on natural numbers
symbol ⊕ₙ : ℕ → ℕ → ℕ; notation ⊕ₙ infix right 10;

rule Oₙ ⊕ₙ $y ↪ $y
with $x ⊕ₙ Oₙ ↪ $x
with sₙ $x ⊕ₙ sₙ $y ↪ sₙ ($x ⊕ₙ $y);

// addition on natural numbers
symbol + : ℕ → ℕ → ℕ; notation + infix right 5;

rule Oₙ + $y ↪ $y
with $x + Oₙ ↪ $x
with sₙ $x + $y ↪ sₙ ($x + $y)
with $x + sₙ $y ↪ sₙ ($x + $y)
with ($x + $y) + $z ↪ $x + ($y + $z);

// s-max algebra: successor iterator and max operator on levels
constant symbol z : L;
symbol s : L → ℕ → L;
right associative commutative symbol ⊕ : L → L → L;
notation ⊕ infix right 10;

// Translation of Agda's levels to the s-max algebra 
rule Z       ↪ s z Oₙ
with S $x    ↪ s $x (sₙ Oₙ)
with $x ∪ $y ↪ $x ⊕ $y
with V $x    ↪ s ($x ⊕ z) Oₙ;

// rules for deciding the s-max algebra
rule s (s $x $p) $q ↪ s $x ($p + $q)
with s ($x ⊕ $y) $p ↪ s $x $p ⊕ s $y $p;

rule s $x $p ⊕ s $x $q ↪ s $x ($p ⊕ₙ $q)
with s $x $p ⊕ (s $x $q ⊕ $y) ↪ s $x ($p ⊕ₙ $q) ⊕ $y;

// tests
assert x y ⊢ ((S (S (V x))) ∪ (S (V y))) ∪ Z ≡ s y (sₙ Oₙ) ⊕ (s x (sₙ(sₙ Oₙ)) ⊕ s z (sₙ(sₙ Oₙ)));
assert a ⊢ s (a ⊕ z) (sₙ Oₙ) ⊕ s (a ⊕ z) (sₙ(sₙ Oₙ)) ≡ s a (sₙ(sₙ Oₙ)) ⊕ s z (sₙ(sₙ Oₙ));
