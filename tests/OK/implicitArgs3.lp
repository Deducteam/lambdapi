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

// Mini interpretation function from code of types to real types
symbol injective T : U ⇒ TYPE
rule T Nat     → N
rule T Bool    → B

// Mini vectors of booleans
symbol const Vect : T Nat ⇒ U

symbol nil : T (Vect zero)

symbol const cons : ∀{n:T Nat}, T (Vect n) ⇒ T Bool ⇒ T (Vect (s n))
// A version in full, without implicit arguments
symbol const consF : ∀(n:T Nat), T (Vect n) ⇒ T Bool ⇒ T (Vect (s n))

// [true], written in full, without implicits arguments
definition l1F : T (Vect (s zero)) ≔ consF zero nil true

// [true]
definition l1  : T (Vect (s zero)) ≔ cons nil true
// It works.

// Same as l1 but fully explicit
definition l2 : T (Vect (s zero)) ≔ @cons zero nil true

