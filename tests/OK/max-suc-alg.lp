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
symbol s : ℕ → L → L;
associative commutative symbol ⊕ : L → L → L; // associative right by default
notation ⊕ infix right 10;

// Translation of Agda's levels to the s-max algebra 
rule Z       ↪ s Oₙ z
with S $x    ↪ s (sₙ Oₙ) $x
with $x ∪ $y ↪ $x ⊕ $y
with V $x    ↪ s Oₙ ($x ⊕ z);

// rules for deciding the s-max algebra
rule s $p (s $q $x) ↪ s ($p + $q) $x
with s $p ($x ⊕ $y) ↪ s $p $x ⊕ s $p $y;

rule s $p $x ⊕ s $q $x ↪ s ($p ⊕ₙ $q) $x
with s $p $x ⊕ (s $q $x ⊕ $y) ↪ s ($p ⊕ₙ $q) $x ⊕ $y;

// tests
assert x y ⊢ ((S (S (V x))) ∪ (S (V y))) ∪ Z ≡ s (sₙ Oₙ) y ⊕ (s (sₙ(sₙ Oₙ)) x ⊕ s (sₙ(sₙ Oₙ)) z);
assert a ⊢ s (sₙ Oₙ) (a ⊕ z) ⊕ s (sₙ(sₙ Oₙ)) (a ⊕ z) ≡ s (sₙ(sₙ Oₙ)) a ⊕ s (sₙ(sₙ Oₙ)) z;
