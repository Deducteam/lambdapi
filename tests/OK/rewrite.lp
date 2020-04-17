// Data type of booleans.

constant symbol B : TYPE

constant symbol true  : B
constant symbol false : B

// Data type of natural numbers.

constant symbol N : TYPE

constant symbol z : N
constant symbol s : N → N

set builtin "0"  ≔ z
set builtin "+1" ≔ s

// Addition on natural numbers.

symbol add : N → N → N

rule add z      $x ↪ $x
rule add (s $x) $y ↪ s (add $x $y)

// Multiplication on natural numbers.

symbol mul : N → N → N

rule mul z      _  ↪ z
rule mul (s $x) $y ↪ add $y (mul $x $y)

// Type of data type codes and their interpretation as types.

constant symbol U : TYPE

symbol T : U → TYPE

constant symbol bool : U
constant symbol nat  : U

rule T bool ↪ B
rule T nat  ↪ N

constant symbol pi : Π (a : U), (T a → U) → U

rule T (pi $a $f) ↪ Π (x : T $a), T ($f x)

// Type of propositions and their interpretation as types.

constant symbol Prop : TYPE

symbol P : Prop → TYPE

constant symbol all : Π (a : U), (T a → Prop) → Prop

rule P (all $a $f) ↪ Π (x : T $a), P ($f x)

// Induction principle on N.

symbol nat_ind : Π (p:N→Prop), P(p z) → (Πn, P(p n) → P(p (s n))) → Πn, P(p n)

rule nat_ind _  $u _  z      ↪ $u
rule nat_ind $p $u $v (s $n) ↪ $v $n (nat_ind $p $u $v $n)

// Boolean equality on N.

symbol beq : N → N → B

rule beq z      z      ↪ true
rule beq (s $x) (s $y) ↪ beq $x $y
rule beq z      (s _ ) ↪ false
rule beq (s _ ) z      ↪ false

// Leibniz equality.

constant symbol eq : Πa, T a → T a → Prop

constant symbol refl : Πa x, P (eq a x x)

constant symbol eqind : Πa x y, P (eq a x y) → Π (p:T a→Prop), P (p y) → P (p x)
// FIXME Try to infer the type of p.

// Setting up builtins for rewrite.

set builtin "P"     ≔ P
set builtin "T"     ≔ T
set builtin "eq"    ≔ eq
set builtin "eqind" ≔ eqind
set builtin "refl"  ≔ refl

// [Π n m, n + S m = S (n+m)]
theorem add_succ_r : Πn m, P (eq nat (add n (s m)) (s (add n m)))
proof
  assume n m
  refine nat_ind (λn, eq nat (add n (s m)) (s (add n m))) ?CZ[n,m] ?CS[n,m] n
  // Case Z.
  simpl
  reflexivity
  // Case S.
  simpl
  assume pn ih
  rewrite ih
  reflexivity
qed

theorem rewriteTest0 : Πx y z,
  P (eq nat (add (add x (s y)) z) (add (s (add x y)) z))
proof
  assume x y z
  print
  rewrite add_succ_r
  refine refl nat (add (s (add x y)) z)
qed


