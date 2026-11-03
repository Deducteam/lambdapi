// additional rewrite rules derived from proved equalities

// Bool

require open tests.OK.Bool;

opaque symbol or_true b:π(b or true = true) ≔ or_true b;
rule _ or true  ↪ true;

opaque symbol or_false b:π(b or false = b) ≔ or_false b;
rule $b or false ↪ $b;

opaque symbol and_true b:π(b and true = b) ≔ and_true b;
rule $b and true ↪ $b;

opaque symbol and_false b:π(b and false = false) ≔ and_false b;
rule _ and false ↪ false;

// Nat

require open tests.OK.Nat;

opaque symbol addn0 x: π(x + _0 = x) ≔ addn0 x;
rule $x + _0 ↪ $x;

opaque symbol addnS x y: π(x + y +1 = (x + y) +1) ≔ addnS x y;
rule $x + $y +1 ↪ ($x + $y) +1;

opaque symbol addnA x y z: π((x + y) + z = x + (y + z)) ≔ addnA x y z;
rule ($x + $y) + $z ↪ $x + ($y + $z);

opaque symbol subn0 x: π(x - _0 = x) ≔ subn0 x;
rule $x - _0 ↪ $x;

opaque symbol muln0 x: π(x * _0 = _0) ≔ muln0 x;
rule _ * _0 ↪ _0;

opaque symbol maxn0 x: π(max x _0 = x) ≔ maxn0 x;
rule max $x _0 ↪ $x;

opaque symbol maxnn x: π(max x x = x) ≔ maxnn x;
rule max $x $x ↪ $x;

opaque symbol minn0 x: π(min x _0 = 0) ≔ minn0 x;
rule min _ _0 ↪ _0;

opaque symbol minnn x: π(min x x = x) ≔ minnn x;
rule min $x $x ↪ $x;

// List

require open tests.OK.List;

opaque symbol cats0 a (m:𝕃 a): π(m ++ □ = m) ≔ cats0 m;
rule $m ++ □ ↪ $m;

opaque symbol size_cat a (l m:𝕃 a): π(size(l ++ m) = size l + size m) ≔ size_cat l m;
rule size ($l ++ $m) ↪ size $l + size $m;

opaque symbol catA a (l m n:𝕃 a): π((l ++ m) ++ n = l ++ (m ++ n)) ≔ catA l m n;
rule ($l ++ $m) ++ $n ↪ $l ++ ($m ++ $n);

opaque symbol lastl a x e (l:𝕃 a): π(last x (e ⸬ l) = last e l) ≔ lastl l x e;
rule last _ ($e ⸬ $l) ↪ last $e $l;

opaque symbol nthx□ a (x:τ a) n: π(nth x □ n = x) ≔ nthx□ n x;
rule nth $x □ _ ↪ $x;

opaque symbol dropx□ a n: π(drop n □ = □ [a]) ≔ dropx□ n;
rule drop _ □ ↪ □;

opaque symbol taken□ a n: π(take n □ = □ [a]) ≔ taken□ n;
rule take _ □ ↪ □;

// Pos

require open tests.OK.Pos;

opaque symbol addnH x: π(add x H = succ x) ≔ addnH x;
rule add $x H ↪ succ $x;

opaque symbol addHn y: π(add H y = succ y) ≔ addHn y;
rule add H $y ↪ succ $y;

opaque symbol ad_carrynH x: π(add_carry x H = add x (O H)) ≔ add_carrynH x;
rule add_carry $x H ↪ add $x (O H);

opaque symbol add_carryHn y: π(add_carry H y = add (O H) y) ≔ add_carryHn y;
rule add_carry H $y ↪ add (O H) $y;

opaque symbol mul_H_right x: π(mul x H = x) ≔ mul_H_right x;
rule mul $x H ↪ $x;

// Z

require open tests.OK.Z;

opaque symbol +Z0 x: π(x + Z0 = x) ≔ +Z0 x;
rule $x + Z0 ↪ $x;
