// test commutative and associative-commutative symbols

constant symbol A : TYPE;

commutative symbol + : A → A → A;
notation + infix 10;
//assert x y ⊢ x + y ≡ y + x;

right associative commutative symbol * : A → A → A;
notation * infix 10;
assert x y ⊢ x * y ≡ y * x;
assert x y z ⊢ (x * y) * z ≡ x * (y * z);
assert x y z ⊢ (x * y) * z ≡ (z * x) * y;

left associative commutative symbol ^ : A → A → A;
notation ^ infix 10;
assert x y ⊢ x ^ y ≡ y ^ x;
assert x y z ⊢ (x ^ y) ^ z ≡ x ^ (y ^ z);
assert x y z ⊢ (x ^ y) ^ z ≡ (z ^ x) ^ y;

// #642

constant symbol z : A;
constant symbol s : A → A;

rule z + $y ↪ $y
with (s $x) + $y ↪ s ($x + $y);

// #644

symbol Nat : TYPE;
symbol plus_N : Nat → Nat → Nat;

symbol Lvl : TYPE;
symbol LvlSet : TYPE;

symbol Max : Nat → LvlSet → Lvl;
symbol Plus : Nat → Lvl → LvlSet;
symbol mapPlus : Nat → LvlSet → LvlSet;

right associative commutative symbol Union : LvlSet → LvlSet → LvlSet;

rule Max $i (Union (Plus $j (Max $k $l)) $tl) ↪ Max (plus_N $i (plus_N $j $k)) (Union (mapPlus $j $l) $tl);

rule Max $i (Union $tl (Plus $j (Max $k $l))) ↪ Max (plus_N $i (plus_N $j $k)) (Union (mapPlus $j $l) $tl);

assert a b c d ⊢ Max c (Union (Plus c (Max c b)) d)
≡ Max (plus_N c (plus_N c c)) (Union (mapPlus c b) d);
