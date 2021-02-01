constant symbol U : TYPE;

// Mini nat
constant symbol Nat  : U;
constant symbol N : TYPE;

// Mini interpretation function
injective symbol T : U → TYPE;
rule T Nat        ↪ N;

constant symbol zero : T Nat;
constant symbol s : N → N;


constant symbol id : Π{Typ:U}, T Typ → T Typ;
// A version in full, without implicit arguments
constant symbol idF : Π(Typ:U), T Typ → T Typ;

// We would like to do :
// symbol zero2 ≔ id zero

// But it won't work for now because we need to find a Typ:U such that
// T Typ = Tgiven
// where Tgiven here is N
// Obviously, we know that T Nat = N, but we don't have yet implemented a way to reverse the
// rewrite rules for T (hoping that T really is injective, otherwise obviously we'll have to make a choice).
// We will need to implement that to make implicit arguments useful for polymorphic symbols,
// but it's beyong the usage of implicit arguments for now

// Question :
// Why is it also failing to work if we declare zero to live in (T Nat) instead of N ?
// Perhaps the unification can't even deal with (T x = T y). If that's the case then first we need to improve the
// unification to make this work
