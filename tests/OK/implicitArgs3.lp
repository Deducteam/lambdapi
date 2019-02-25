symbol const U : TYPE

// Mini bool
symbol const Bool : U
symbol const B : TYPE
symbol true : B
symbol false : B

// Mini nat
symbol const Nat  : U
symbol const N : TYPE
symbol const zero : N
symbol const s : N ⇒ N
symbol add : N ⇒ N ⇒ N
set infix left 6 "+" ≔ add

rule zero   + &n     → &n
rule (s &m) + &n     → s (&m + &n)
rule &m     + zero   → &m
rule &m     + (s &n) → s (&m + &n)

// Mini interpretation function from code of types to real types
symbol injective T : U ⇒ TYPE
rule T Nat     → N
rule T Bool    → B

// Mini vectors of booleans
symbol const Vect : T Nat ⇒ U

symbol nil : T (Vect zero)

symbol const cons : ∀{n:T Nat}, T Bool ⇒ T (Vect n) ⇒ T (Vect (s n))

// TEST IMPLICIT ARGUMENTS FOR A DEFINITION, WITHOUT THE @ MARKER
// [true]
definition l1  : T (Vect (s zero)) ≔ cons true nil
// It works.

// TEST IMPLICIT ARGUMENTS FOR A DEFINITION, WITH THE @ MARKER
// Same as l1 but fully explicit
definition l2 : T (Vect (s zero)) ≔ @cons zero true nil
// It works.

symbol append : ∀ (n:T Nat) (m:T Nat), T (Vect n) ⇒ T (Vect m) ⇒ T (Vect (n+m))
// Unfortunately, we can't use implicit in rules at the moment
rule append zero    &m nil                   &v2  → &v2
rule append (s &pn) &m (@cons (s &pn) &h &t) &v2  → @cons (&pn+&m) &h (append &pn &m &t &v2)


// TEST IMPLICIT ARGUMENTS FOR DEFINITION
// definition id_Vect : ∀{n:T Nat}, T (Vect n) ⇒ T(Vect n) ≔ λx, x
// Doesn't work yet

// TEST IMPLICIT ARGUMENTS FOR THEOREM
//Theorem append_assoc : ∀{n1:T Nat} {n2:T Nat} {n3:T Nat}
//                        (v1:T (Vect n1)) (v2:T (Vect n2)) (v3:T (Vect n3)),
//  append n1 (n2+n3) v1 (append v2 v3) = append (n1+n2) (append n1 n2 v1 v2) v3

