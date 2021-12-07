constant symbol U : TYPE;

// Mini bool
constant symbol Bool : U;
constant symbol B : TYPE;
symbol true : B;
symbol false : B;

// Mini nat
constant symbol Nat  : U;
constant symbol N : TYPE;
constant symbol zero : N;
constant symbol s : N → N;
symbol + : N → N → N;
notation + infix left 6;

rule zero   + $n     ↪ $n;
rule (s $m) + $n     ↪ s ($m + $n);
rule $m     + zero   ↪ $m;
rule $m     + (s $n) ↪ s ($m + $n);

// Mini interpretation function from code of types to real types
injective symbol T : U → TYPE;

rule T Nat     ↪ N;
rule T Bool    ↪ B;

// Mini vectors of booleans
constant symbol Vect : T Nat → U;

symbol nil : T (Vect zero);

// The nat is declared to be implicit
constant symbol cons : Π[n:T Nat], T Bool → T (Vect n) → T (Vect (s n));

// TEST IMPLICIT ARGUMENTS FOR A DEFINITION, WITHOUT THE @ MARKER
// [true]
symbol l1  : T (Vect (s zero)) ≔ cons true nil;
// It works.

// TEST NESTED IMPLICIT ARGUMENTS FOR A DEFINITION, WITHOUT THE @ MARKER
symbol l2 : T (Vect (s (s zero))) ≔ cons true (cons false nil);
// It works

// TEST IMPLICIT ARGUMENTS FOR A DEFINITION, WITH THE @ MARKER
// Same as l1 but fully explicit
symbol l3 : T (Vect (s zero)) ≔ @cons zero true nil;
// It works.

// TEST NESTED IMPLICIT ARGUMENTS FOR A DEFINITION, WITH THE @ MARKER
// Same as l2 but fully explicit
symbol l4 : T (Vect (s (s zero))) ≔ @cons (s zero) true (@cons zero false nil);
// It works.

symbol append : Π (n:T Nat) (m:T Nat), T (Vect n) → T (Vect m) → T (Vect (n + m));
// Works, but unfortunately, we can't use implicits in RHS of rewrite rules at the moment
rule append zero    $m nil           $v2  ↪ $v2;
rule append (s $pn) $m (cons $h $t)  $v2  ↪ @cons ($pn + $m) $h (append $pn $m $t $v2);

rule append (s $pn) $m (cons $h $t)  $v2  ↪ cons [$pn + $m] $h (append $pn $m $t $v2);
