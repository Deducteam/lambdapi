// Data type of booleans.

symbol const B : TYPE

symbol const true  : B
symbol const false : B

// Data type of natural numbers.

symbol const N : TYPE

symbol const z : N
symbol const s : N ⇒ N

definition one ≔ s z
definition two ≔ s one

// Addition on natural numbers.

symbol add : N ⇒ N ⇒ N

rule add z      &x → &x
rule add (s &x) &y → s (add &x &y)

// Multiplication on natural numbers.

symbol mul : N ⇒ N ⇒ N

rule mul z      _  → z
rule mul (s &x) &y → add &y (mul &x &y)

// Type of data type codes and their interpretation as types.

symbol const U : TYPE

symbol T : U ⇒ TYPE

symbol const bool : U
symbol const nat  : U

rule T bool → B
rule T nat  → N

symbol const pi : ∀ (a : U), (T a ⇒ U) ⇒ U

rule T (pi &a &f) → ∀ (x : T &a), T (&f x)

// Type of propositions and their interpretation as types.

symbol const Prop : TYPE

symbol P : Prop ⇒ TYPE

symbol const all : ∀ (a : U), (T a ⇒ Prop) ⇒ Prop

rule P (all &a &f) → ∀ (x : T &a), P (&f x)

// Induction principle on N.

symbol nat_ind : ∀ (p:N⇒Prop), P(p z) ⇒ (∀n, P(p n) ⇒ P(p (s n))) ⇒ ∀n, P(p n)

rule nat_ind _  &u _  z      → &u
rule nat_ind &p &u &v (s &n) → &v &n (nat_ind &p &u &v &n)

// Boolean equality on N.

symbol beq : N ⇒ N ⇒ B

rule beq z      z      → true
rule beq (s &x) (s &y) → beq &x &y
rule beq z      (s _ ) → false
rule beq (s _ ) z      → false

// Leibniz equality.

symbol const eq : ∀a, T a ⇒ T a ⇒ Prop

symbol const refl : ∀a x, P (eq a x x)

symbol const eqind : ∀a x y, P (eq a x y) ⇒ ∀ (p:T a⇒Prop), P (p y) ⇒ P (p x)
// FIXME Try to infer the type of p.

// [∀ n m, n + S m = S (n+m)]
theorem add_succ_r : ∀n m, P (eq nat (add n (s m)) (s (add n m)))
proof
  intro n m
  refine nat_ind (λn, eq nat (add n (s m)) (s (add n m))) ?CZ[n,m] ?CS[n,m] n
  // Case Z.
  simpl
  refine refl nat (s m) // TODO add a reflexivity tactic
  // Case S.
  simpl
  intro pn ih
  rewrite ih
  refine refl nat (s (s (add pn m)))
qed

theorem rewriteTest0 : ∀x y z,
  P (eq nat (add (add x (s y)) z) (add (s (add x y)) z))
proof
  intro x y z
  print
  rewrite add_succ_r
  refine refl nat (add (s (add x y)) z)
qed


