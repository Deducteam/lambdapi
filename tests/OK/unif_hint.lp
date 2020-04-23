// Simple unification hints
symbol U: TYPE
symbol T: U → TYPE
symbol bool: U
symbol Bool: TYPE
rule T bool ↪ Bool

//   &x ≡ bool
// --------------
//  T &x ≡ Bool
hint (T $x) ≡ Bool ↪ $x ≡ bool

symbol f : (Bool → Bool) → U

type f (λx: T _, x)

symbol Nat: TYPE
symbol nat: U
rule T nat ↪ Nat

//   &x ≡ nat
// -------------
//  T &x ≡ Nat
hint (T $x) ≡ Nat ↪ $x ≡ nat

symbol G: Bool → Nat → TYPE
type λx: T _, λy: T _, G x y

// Need several hints
symbol z: Nat
symbol s: Nat → Nat
symbol plus : Nat → Nat → Nat
rule plus z $n      ↪ $n
with plus (s $m) $n ↪ s (plus $m $n)

injective symbol I: Nat → TYPE
symbol H (n: Nat): I n → Nat
symbol iz: I z
//    &x ≡ z   &y ≡ z
// -------------------
//    plus &x &y ≡ z
hint (plus $x $y) ≡ z ↪ $x ≡ z, $y ≡ z
// Trigger the unification problem plus ?1 ?2 ≡ z
compute H (plus _ _) iz

// The arrow problem
symbol arrow : U → U → U
rule T (arrow $t $u) ↪ T $t → T $u
// hint (T $a → T $b) ≡ T (arrow $c $d) ↪ $a ≡ $c, $b ≡ $d
// FIXME: implications not allowed in LHS (scoping level)
