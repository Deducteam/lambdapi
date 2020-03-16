// Simple unification hints
symbol U: TYPE
symbol T: U ⇒ TYPE
symbol bool: U
symbol Bool: TYPE
rule T bool → Bool

//   &x ≡ bool
// --------------
//  T &x ≡ Bool
hint hint_unif (T &x) Bool → hint_unif &x bool

symbol f : (Bool ⇒ Bool) ⇒ U

type f (λx: T _, x)

symbol Nat: TYPE
symbol nat: U
rule T nat → Nat

//   &x ≡ nat
// -------------
//  T &x ≡ Nat
hint hint_unif (T &x) Nat → hint_unif &x nat

symbol G: ∀(x: Bool) (y: Nat), TYPE
type λx: T _, λy: T _, G x y

// Need several hints
symbol z: Nat
symbol s: Nat ⇒ Nat
symbol plus : Nat ⇒ Nat ⇒ Nat
rule plus z &n      → &n
 and plus (s &m) &n → s (plus &m &n)

injective symbol I (n: Nat): TYPE
symbol H (n: Nat): I n ⇒ Nat
symbol iz: I z
hint hint_unif (plus &x &y) z → hint_conj (hint_unif &x z) (hint_unif &y z)
// Trigger the unification problem plus ?1 ?2 ≡ z
compute H (plus _ _) iz
