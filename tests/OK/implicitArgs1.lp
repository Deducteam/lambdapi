symbol const U : TYPE

// Mini nat
symbol const Nat  : U
symbol const N : TYPE

// Mini interpretation function
symbol injective T : U ⇒ TYPE
rule T Nat        → N

symbol const zero : T Nat
symbol const s : N ⇒ N



// Mini polymorphic lists
symbol const List : U ⇒ U

symbol const nil : ∀{Typ:U}, T(List Typ)
// A version in full, without implicit arguments
symbol const nilF : ∀(Typ:U), T(List Typ)

symbol const cons : ∀{Typ:U}, T Typ ⇒ T (List Typ) ⇒ T (List Typ)
// A version in full, without implicit arguments
symbol const consF : ∀(Typ:U), T Typ ⇒ T (List Typ) ⇒ T (List Typ)


definition l1F ≔ consF Nat zero (nilF Nat)

// This won't work due to the fact that solving
// without declaring zero : T Nat instead of zero : N
// definition l1 ≔ cons zero nil