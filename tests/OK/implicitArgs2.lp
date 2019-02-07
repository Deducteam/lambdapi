symbol const U : TYPE

// Mini nat
symbol const Nat  : U
symbol const N : TYPE

// Mini interpretation function
symbol injective T : U ⇒ TYPE
rule T Nat        → N

symbol const zero : T Nat
symbol const s : N ⇒ N


symbol const id : ∀{Typ:U}, T Typ ⇒ T Typ
// A version in full, without implicit arguments
symbol const idF : ∀(Typ:U), T Typ ⇒ T Typ

definition zero2 ≔ id zero


