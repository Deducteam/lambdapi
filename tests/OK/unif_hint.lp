// Simple unification hints
symbol U: TYPE;
injective symbol T: U → TYPE;
symbol bool: U;
symbol Bool: TYPE;
rule T bool ↪ Bool;

//   &x ≡ bool
// --------------
//  T &x ≡ Bool
set unif_rule (T $x) ≡ Bool ↪ [ $x ≡ bool ];

symbol f : (Bool → Bool) → U;

type f (λ x: T _, x);

symbol Nat: TYPE;
symbol nat: U;
rule T nat ↪ Nat;

//   &x ≡ nat
// -------------
//  T &x ≡ Nat
set unif_rule T $x ≡ Nat ↪ [ $x ≡ nat ];

symbol G: Bool → Nat → TYPE;
type λ x: T _, λ y: T _, G x y;

// Need several hints
symbol z: Nat;
symbol s: Nat → Nat;
symbol plus : Nat → Nat → Nat;
rule plus z $n      ↪ $n
with plus (s $m) $n ↪ s (plus $m $n);

injective symbol I: Nat → TYPE;
symbol H (n: Nat): I n → Nat;
symbol iz: I z;
//    &x ≡ z   &y ≡ z
// -------------------
//    plus &x &y ≡ z
set unif_rule (plus $x $y) ≡ z ↪ [ $x ≡ z; $y ≡ z ];
// Trigger the unification problem plus ?1 ?2 ≡ z
compute H (plus _ _) iz;

constant symbol Pair: U → TYPE;
constant symbol pair {t: U}:  T t → T t → Pair t;
symbol fst {t}: Pair t → T t;
symbol snd {t}: Pair t → T t;
set unif_rule fst $p ≡ $f ↪ [ $p ≡ pair $f $s ];
set unif_rule snd $p ≡ $s ↪ [ $p ≡ pair $f $s ];
constant symbol K {t}: T t → TYPE;
constant symbol J {t} (p: Pair t): K (fst p) → TYPE;
constant symbol kz: K z;
compute J (pair _ z) kz;

// The arrow problem
symbol arrow : U → U → U;
rule T (arrow $t $u) ↪ T $t → T $u;
set unif_rule $a → $b ≡ T $c ↪ [ $a ≡ T $ea; $b ≡ T $eb; $c ≡ arrow $ea $eb ];
symbol eq (t: U): T t → T t → Bool;
compute eq _ (λ _, z) (λ _, z);
