require open tests.OK.Z tests.OK.Pos;

constant symbol R : TYPE;

symbol var : ℤ → ℤ → R;
/* semantics: [var x k] = x * k
note that the first argument could be of any type that has a ring structure
(we then would take R : TYPE → TYPE) */
constant symbol cst:ℤ → R;
symbol opp:R → R;
right associative commutative symbol add:R → R → R;

rule var _ 0 ↪ cst 0;

rule opp (var $x $k) ↪ var $x (— $k)
with opp (cst $k) ↪ cst (— $k)
with opp (opp $x) ↪ $x
with opp (add $x $y) ↪ add (opp $x) (opp $y);
// note that opp is totally defined on terms built with var, cst, opp and add, i.e. no normal form contains opp

rule add (var $x $k) (var $x $l) ↪ var $x ($k + $l)
with add (var $x $k) (add (var $x $l) $y) ↪ add (var $x ($k + $l)) $y
with add (cst $k) (cst $l) ↪ cst ($k + $l)
with add (cst $k) (add (cst $l) $y) ↪ add (cst ($k + $l)) $y
with add (cst 0) $x ↪ $x
with add $x (cst 0) ↪ $x;

// example:
compute λ x y z, add (add (var x 1) (add (opp (var y 1)) (var z 1))) (add (var y 1) (var x 1));
assert x y z ⊢ add (add (var x 1) (add (opp (var y 1)) (var z 1))) (add (var y 1) (var x 1)) ≡ add (var x 2) (var z 1);

// multiplication by a constant (optional)
symbol mul:ℤ → R → R;
rule mul $k (var $z $l) ↪ var $z ($k * $l)
with mul $k (opp $r) ↪ mul (— $k) $r
with mul $k (add $r $s) ↪ add (mul $k $r) (mul $k $s)
with mul $k (cst $z) ↪ cst ($k * $z)
with mul $k (mul $l $z) ↪ mul ($k * $l) $z;
// note that mul is totally defined on terms built from var, cst, opp, add and mul, i.e. no normal form contains mul

// reification
// WARNING: this symbol is declared as sequential
// and the reduction relation is not stable by substitution
sequential symbol ⇧ : ℤ → R;

rule ⇧ 0 ↪ cst 0
with ⇧ (Zpos $x) ↪ cst (Zpos $x)
with ⇧ (Zneg $x) ↪ cst (Zneg $x)
with ⇧ (— $x) ↪ opp (⇧ $x)
with ⇧ ($x + $y) ↪ add (⇧ $x) (⇧ $y)

with ⇧ (0 * $y) ↪ mul 0 (⇧ $y)
with ⇧ (Zpos $x * $y) ↪ mul (Zpos $x) (⇧ $y)
with ⇧ (Zneg $x * $y) ↪ mul (Zneg $x) (⇧ $y)
with ⇧ ($y * 0) ↪ mul 0 (⇧ $y)
with ⇧ ($y * Zpos $x) ↪ mul (Zpos $x) (⇧ $y)
with ⇧ ($y * Zneg $x) ↪ mul (Zneg $x) (⇧ $y)

with ⇧ $x ↪ var $x 1; // must be the last rule for ⇧

// example:
compute λ x y z, ⇧ ((x + ((— y) + z)) + (y + x));
compute λ x, ⇧ ((— x - — 5) + x + — 4);

assert (x y z:ℤ) ⊢ ⇧ ((x + ((— y) + z)) + (y + x)) ≡ ⇧ (2 * x + z);
assert (x:ℤ) ⊢ ⇧ ((— x - — 5) + x + — 4) ≡ ⇧ 1;
