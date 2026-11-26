// From "Checking Linear Integer Arithmetic Proofs in Lambdapi"
// Alessio Coltellacci and Stephan Merz

require open tests.OK.Z;

symbol G : TYPE;

associative commutative symbol ⊕ : G → G → G;
notation ⊕ infix 10;
symbol cst : ℤ → G;
symbol var : ℤ → ℤ → G;
symbol opp : G → G;
symbol ⊗ : ℤ → G → G;
notation ⊗ infix left 12;

rule (var $c1 $x) ⊕ (var $c2 $x) ↪ var ($c1 + $c2) $x
with (var $c1 $x) ⊕ (var $c2 $x ⊕ $y) ↪ var ($c1 + $c2) $x ⊕ $y
with cst $c1 ⊕ cst $c2 ↪ cst ($c1 + $c2)
with cst $c1 ⊕ (cst $c2 ⊕ $x) ↪ cst ($c1 + $c2) ⊕ $x
with cst Z0 ⊕ $x ↪ $x
with $x ⊕ cst Z0 ↪ $x
with opp (var $c $x) ↪ var (— $c) $x
with opp (cst $c) ↪ cst (— $c)
with opp (opp $x) ↪ $x
with opp ($x ⊕ $y) ↪ opp $x ⊕ opp $y
with opp ($k ⊗ $x) ↪ (— $k) ⊗ $x
with $k ⊗ var $c $x ↪ var ($k * $c) $x
with $k ⊗ (opp $x) ↪ (— $k) ⊗ $x
with $k ⊗ ($x ⊕ $y) ↪ $k ⊗ $x ⊕ $k ⊗ $y
with $k ⊗ cst $c ↪ cst ($k * $c)
with $c1 ⊗ $c2 ⊗ $x ↪ ($c1 * $c2) ⊗ $x;

symbol ⇓ : G → ℤ;
rule ⇓ (cst $c) ↪ $c
with ⇓ (var $c $x) ↪ $c * $x
with ⇓ (opp $x) ↪ — (⇓ $x)
with ⇓ ($c ⊗ $x) ↪ $c * (⇓ $x)
with ⇓ ($x ⊕ $y) ↪ ⇓ $x + ⇓ $y;

sequential symbol ⇑ : ℤ → G;
rule ⇑ Z0 ↪ cst Z0
with ⇑ (Zpos $c) ↪ cst (Zpos $c)
with ⇑ (Zneg $c) ↪ cst (Zneg $c)
with ⇑ ($x + $y) ↪ (⇑ $x) ⊕ (⇑ $y)
with ⇑ (— $x) ↪ opp (⇑ $x)
with ⇑ ((Zpos $c) * $x) ↪ (Zpos $c) ⊗ ⇑ $x
with ⇑ ((Zneg $c) * $x) ↪ (Zneg $c) ⊗ ⇑ $x
with ⇑ ($x * (Zpos $c)) ↪ (Zpos $c) ⊗ ⇑ $x
with ⇑ ($x * (Zneg $c)) ↪ (Zneg $c) ⊗ ⇑ $x
with ⇑ (_ * Z0) ↪ cst Z0
with ⇑ (Z0 * _) ↪ cst Z0
with ⇑ $x ↪ var _1 $x;

symbol ⇓⇑ (x: ℤ): π (x = ⇓ (⇑ x));
