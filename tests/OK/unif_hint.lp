// Simple unification hints
symbol U: TYPE
symbol T: U → TYPE
symbol bool: U
symbol Bool: TYPE
rule T bool ↪ Bool

//   &x ≡ bool
// --------------
//  T &x ≡ Bool
set unif_rule (T $x) ≡ Bool ↪ $x ≡ bool

symbol f : (Bool → Bool) → U

type f (λx: T _, x)

symbol Nat: TYPE
symbol nat: U
rule T nat ↪ Nat

//   &x ≡ nat
// -------------
//  T &x ≡ Nat
set unif_rule T $x ≡ Nat ↪ $x ≡ nat

symbol G: Bool → Nat → TYPE
type λx: T _, λy: T _, G x y

// Need several hints
symbol z: T nat
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
set unif_rule (plus $x $y) ≡ z ↪ $x ≡ z, $y ≡ z
// Trigger the unification problem plus ?1 ?2 ≡ z
compute H (plus _ _) iz

// The arrow problem
symbol arrow : U → U → U
rule T (arrow $t $u) ↪ T $t → T $u

/// This rule does not work because [T nat] gets reduced to [Nat] during ]
/// matching, and so matching with rule fails.
// set unif_rule (T $a → T $b) ≡ T $c ↪ arrow $a $b ≡ $c

/// This rule works, but is very ad-hoc
// set unif_rule (Nat → Nat) ≡ T $a ↪ arrow nat nat ≡ $a

/// This rule fails because it requires allowing metavariables in rules
// set unif_rule ($a → $b) ≡ T $c ↪ $a ≡ T ?u, $b ≡ T ?v, arrow ?u ?v ≡ $c

/// This rule fails because there is a bug in rewriting, the rhs ends with
/// a pattern variable.
set unif_rule ($a → $b) ≡ T $c ↪ $a ≡ T _, $b ≡ T _, arrow _ _ ≡ $c

symbol eq (t: U): T t → T t → Bool
compute eq _ (λ_: T _, z) (λ_: T _, z)
