// Simple unification hints
symbol Set: TYPE;
injective symbol El: Set → TYPE;
symbol bool: Set;
symbol Bool: TYPE;
rule El bool ↪ Bool;

symbol Nat: TYPE;
symbol nat: Set;
rule El nat ↪ Nat;

// Need several hints
symbol z: Nat;
symbol s: Nat → Nat;
symbol + : Nat → Nat → Nat;
rule + z $n      ↪ $n
with + (s $m) $n ↪ s (+ $m $n);

injective symbol I: Nat → TYPE;
// Assuming [in] is of type [I n], typing [H m in] forces the unification
// problem [m ≡? n].
symbol H (n: Nat): I n → Nat;
symbol iz: I z;
//    &x ≡ z   &y ≡ z
// -------------------
//    + &x &y ≡ z
unif_rule (+ $x $y) ≡ z ↪ [ $x ≡ z; $y ≡ z ];
// Trigger the unification problem + ?1 ?2 ≡ z
type H (+ _ _) iz;

constant symbol Pair: Set → TYPE;
constant symbol pair [t: Set]:  El t → El t → Pair t;
symbol fst [t]: Pair t → El t;
symbol snd [t]: Pair t → El t;
unif_rule fst $p ≡ $f ↪ [ $p ≡ pair $f $s ];
unif_rule snd $p ≡ $s ↪ [ $p ≡ pair $f $s ];
constant symbol K [t]: El t → TYPE;
constant symbol J [t] (p: Pair t): K (fst p) → TYPE;
constant symbol kz: K z;
compute J (pair _ z) kz;

// The arrow problem
constant symbol arrow : Set → Set → Set;
rule El (arrow $t $u) ↪ El $t → El $u;
unif_rule $a → $b ≡ El $c ↪ [ $a ≡ El $ea; $b ≡ El $eb; $c ≡ arrow $ea $eb ];
symbol eq (t: Set): El t → El t → Bool;
type eq _ (λ _, z) (λ _, z);

constant symbol Vec (n: Nat): Set;
constant symbol vec (n: Nat): El (Vec n);

// Dependent arrow
constant symbol darr : Π a: Set, (El a → Set) → Set;
rule El (darr $d (λ x: El _, $c.[x])) ↪ Π z : El $d, El ($c.[z]);
unif_rule El $e ≡ Π x : $a, $b.[x] ↪
  [ $a ≡ El $sa // $a must be an encoded type
  ; (λ x: El $sa, $b.[x]) ≡ (λ x: El $sa, El $sb.[x])
    // $b as well, but with a bound variable
  ; $e ≡ darr $sa (λ z: El $sa, $sb.[z]) ];
type eq _ vec vec;
