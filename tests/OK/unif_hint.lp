// Simple unification hints
symbol U: TYPE
symbol T: U ⇒ TYPE
symbol bool: U
symbol Bool: TYPE
rule T bool → Bool
hint hint_unif (T &x) Bool → hint_unif &x bool

symbol f : (Bool ⇒ Bool) ⇒ U

type f (λx: T _, x)

symbol Nat: TYPE
symbol nat: U
rule T nat → Nat
hint hint_unif (T &x) Nat → hint_unif &x nat

symbol G: ∀(x: Bool) (y: Nat), TYPE
type λx: T _, λy: T _, G x y
