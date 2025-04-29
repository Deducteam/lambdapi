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

// eval function
symbol ⇓: R → ℤ;
rule ⇓ (var $k $x) ↪ $k * $x
with ⇓ (cst $k) ↪ $k
with ⇓ (opp $x) ↪ — (⇓ $x)
with ⇓ (add $x $y) ↪ ⇓ $x + ⇓ $y;

require open tests.OK.Set;

symbol T1: τ int;
symbol T2: τ int;
symbol T3: τ int;
symbol T4: τ int;
symbol T5: τ int;
symbol T6: τ int;
symbol T7: τ int;
symbol T8: τ int;
symbol T9: τ int;
symbol T10: τ int;
symbol T11: τ int;
symbol T12: τ int;
symbol T13: τ int;
symbol T14: τ int;
symbol T15: τ int;
symbol T16: τ int;
symbol T17: τ int;
symbol T18: τ int;
symbol T19: τ int;
symbol T20: τ int;
symbol T21: τ int;
symbol T22: τ int;
symbol T23: τ int;
symbol T24: τ int;
symbol T25: τ int;
symbol T26: τ int;
symbol T27: τ int;
symbol T28: τ int;
symbol T29: τ int;
symbol T30: τ int;
symbol T31: τ int;
symbol T32: τ int;
symbol T33: τ int;
symbol T34: τ int;
symbol T35: τ int;
symbol T36: τ int;
symbol T37: τ int;
symbol T38: τ int;
symbol T39: τ int;
symbol T40: τ int;

symbol t1 ≔ (⇧
    (
        (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8 + T9 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20)
        + (
            (— 1) * (T20 + T19 + T18 + T17 + T16 + T15 + T14 + T13 + T12 + T11 + T10 + T9 + T8 + T7 + T6 + T5 + T4 + T3 + T2 + T1)
        )
    )
);
compute t1;
assert ⊢ t1 ≡ ⇧ 0;

symbol t2 ≔ (⇧
    (
        (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8 + T9 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22)
        + (
            (— 1) * (T22 + T21 + T20 + T19 + T18 + T17 + T16 + T15 + T14 + T13 + T12 + T11 + T10 + T9 + T8 + T7 + T6 + T5 + T4 + T3 + T2 + T1)
        )
    )
);
compute t2;
assert ⊢ t2 ≡ ⇧ 0;

symbol t3 ≔ (⇧
    (
        (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8 + T9 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23)
        + (
            (— 1) * (T23 + T22 + T21 + T20 + T19 + T18 + T17 + T16 + T15 + T14 + T13 + T12 + T11 + T10 + T9 + T8 + T7 + T6 + T5 + T4 + T3 + T2 + T1)
        )
    )
);
compute t3;
assert ⊢ t3 ≡ ⇧ 0;

symbol t4 ≔ (⇧
    (
        (T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8 + T9 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28 + T29 + T30 + T31 + T32 + T33 + T34 + T35 + T36 + T37 + T38 + T39 + T40)
        + (
            (— 1) * (T40 + T39 + T38 + T37 + T36 + T35 + T34 + T33 + T32 + T31 + T30 + T29 + T28 + T27 + T26 + T25 + T24 + T23 + T22 + T21 + T20 + T19 + T18 + T17 + T16 + T15 + T14 + T13 + T12 + T11 + T10 + T9 + T8 + T7 + T6 + T5 + T4 + T3 + T2 + T1)
        )
    )
);
compute t4;
assert ⊢ t4 ≡ ⇧ 0;
