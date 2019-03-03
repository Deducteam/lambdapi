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

// We would like to do :
// definition zero2 ≔ id zero

// But it won't work for now because we need to find a Typ:U such that
// T Typ = Tgiven
// where Tgiven here is N
// Obviously, we know that T Nat = N, but we don't have yet implemented a way to reverse the
// rewrite rules for T (hoping that T really is injective, otherwise obviously we'll have to make a choice).
// We will need to implement that to make implicit arguments useful for polymorphic definitions,
// but it's beyong the usage of implicit arguments for now

// Question :
// Why is it also failing to work if we declare zero to live in (T Nat) instead of N ?
// Perhaps the unification can't even deal with (T x = T y). If that's the case then first we need to improve the
// unification to make this work
