constant symbol U : TYPE;

// Mini nat
constant symbol Nat  : U;
constant symbol N : TYPE;

// Mini interpretation function
injective symbol T : U → TYPE;
rule T Nat        ↪ N;

constant symbol zero : T Nat;
constant symbol s : N → N;



// Mini polymorphic lists
constant symbol List : U → U;

constant symbol nil : Π[Typ:U], T(List Typ);
// A version in full, without implicit arguments
constant symbol nilF : Π(Typ:U), T(List Typ);

constant symbol cons : Π[Typ:U], T Typ → T (List Typ) → T (List Typ);
// A version in full, without implicit arguments
constant symbol consF : Π(Typ:U), T Typ → T (List Typ) → T (List Typ);


symbol l1F ≔ consF Nat zero (nilF Nat);

// We would like to do :
// symbol l1 ≔ cons zero nil

// But it won't work for now because we need to find a Typ:U such that
// T Typ = Tgiven
// where Tgiven here is N
// Obviously, we know that T Nat = N, but we don't have yet implemented a way to reverse the
// rewrite rules for T (hoping that T really is injective, otherwise obviously we'll have to make a choice).
// We will need to implement that to make implicit arguments useful for polymorphic symbols,
// but it's beyong the usage of implicit arguments for now
