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

// We would like to do :
// definition l1 ≔ cons zero nil

// But it won't work for now because we need to find a Typ:U such that
// T Typ = Tgiven
// where Tgiven here is N
// Obviously, we know that T Nat = N, but we don't have yet implemented a way to reverse the
// rewrite rules for T (hoping that T really is injective, otherwise obviously we'll have to make a choice).
// We will need to implement that to make implicit arguments useful for polymorphic definitions,
// but it's beyong the usage of implicit arguments for now
