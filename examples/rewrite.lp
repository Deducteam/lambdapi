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
//rule mul (s &x) &y → add &y (mul &x ay) // FIXME scoping bug
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

// Symmetry of the equality.
theorem eq_sym : ∀a x y, P (eq a x y) ⇒ P (eq a y x)
proof
  intro a x y h
  //rewrite h
//(; First option, doing the proof via rewrite ;)
//#REWRITE H.
//#REFINE (refl a y).
//(; Second option, by hand, and full ;)
//(;
//#REFINE eqind a x y H (z => eq a y z) (refl a y).
//;)
//(; Third option, by hand, with a wildcard ;)
//(;
//#REFINE eqind a x y H (z => eq a y z) _.
//#SIMPL.
//#REFINE refl a y.
//;)
admit

// [s] is compatible with Leibniz equality.
theorem s_eq : ∀x y, P (eq nat x y) ⇒ P (eq nat (s x) (s y))
proof
  intro x y xy
  refine eqind nat x y xy (λz, eq nat (s z) (s y)) (refl nat (s y))
qed

// [z] is right neutral for add.
theorem add0r : ∀n, P (eq nat (add n z) n)
proof
  // FIXME try to infer nat.
  // FIXME try to infer the predicate
  refine nat_ind (λn, eq nat (add n z) n) ?CZ ?CS
  // Case Z
  simpl
  refine refl nat z
  // Case S
  intro n h
  simpl
  refine s_eq (add n z) n h
qed

// [∀ n m, n + S m = S (n+m)]
theorem add_succ_r : ∀n m, P (eq nat (add n (s m)) (s (add n m)))
proof
  intro n m
  refine nat_ind (λn, eq nat (add n (s m)) (s (add n m))) ?CZ[n,m] ?CS[n,m] n
  // Case Z
  simpl
  refine refl nat (s m)
  // Case S
  simpl
  intro pn ih
  print
//#REWRITE ih.
//#SIMPL.
//#REFINE refl nat (s (s (add pn m))).
admit

// Commutativity of the addition.
theorem addcomm : ∀n m, P (eq nat (add n m) (add m n))
proof
//#REFINE n => m => _.
//#REFINE (nat_ind (n:N => eq nat (add n m) (add m n)) ?case0[n,m] ?caseS[n,m] n).
//(; Case 0 ;)
//#SIMPL.
//#REFINE eq_sym nat (add m 0) m (add0r m). (; TO DO : Add a #SYM tactic ;)
//(; Case S ;)
//#SIMPL.
//#REFINE n => ih => _.
//#REWRITE ih.
//#REWRITE add_succ_r m n0.
//#REFINE refl nat (s (add m n0)).
admit

// Adding the same value is the same as multiplying by 2.
theorem add_same_times_two : ∀x, P (eq nat (add x x) (mul two x))
proof
//#REFINE x => _.
//#SIMPL.
//#REWRITE add0r.
//#REFINE refl nat (add x x).
admit

//////////////////////////////////////////////////////////////////////////////
// Rewrite tests with quantified variables in the hypothesis.               //
//////////////////////////////////////////////////////////////////////////////

// This stupid test directly uses the addcomm lemma.
theorem rewriteTest1 : ∀a b, P (eq nat (add a b) (add b a))
proof
//#REFINE a => b => _.
//#PRINT.
//#REWRITE [add _ b] addcomm.
//#REFINE refl nat (add b a).
admit

// This stupid test directly uses the addcomm lemma in one place.
theorem rewriteTest2 : ∀a b, P (eq nat (add (add a b) b) (add (add b a) b))
proof
//#REFINE a => b => _.
//#REWRITE [X #in (add X b)] addcomm.
//#REFINE refl nat (add (add b a) b).
admit

// This stupid test directly uses the addcomm lemma in two places.
theorem rewriteTest3 : ∀a b,
  P (eq nat (add (add (add a b) b) (add (add a b) b))
            (add (add (add b a) b) (add (add b a) b)))
proof
//#REFINE a => b => _.
//#PRINT.
//#REWRITE [X #in (add X b)] addcomm.
//#REFINE refl nat (add (add (add b a) b) (add (add b a) b)).
admit

// An easy contextual rewrite.
theorem rewriteTest4 : ∀a b,
  P (eq nat (add (add (add a b) (add a b)) a)
            (add (add (add b a) (add a b)) a))
proof
//#REFINE a => b => _.
//#REWRITE [X #in (add X (add a b))] addcomm.
//#REFINE refl nat (add (add (add b a) (add a b)) a).
admit

// A slightly more complicated contextual rewrite.
theorem rewriteTest5 : ∀a b,
  P (eq nat (add (add a b) (add a b)) (add (add b a) (add b a)))
proof
//#REFINE a => b => _.
//#REWRITE [X #in (add X X)] addcomm.
//#REFINE refl nat (add (add b a) (add b a)).
admit

// An even more complicated rewrite, combining both wildcards and binders.
theorem rewriteTest6 : ∀a b,
  P (eq nat (add (add (add a b) a) a) (add (add a (add a b)) a))
proof
//#PRINT.
//#REFINE a => b => _.
//#REWRITE [X #in (add X _)] addcomm.
//#REFINE refl nat (add (add a (add a b)) a).
admit

// Example 17: Very trivial SSReflect example.
symbol silly_axiom : ∀m n, P (eq nat m n)

theorem rewriteTest7 : ∀a b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
proof
//#REFINE a => b => c => _.
//#REWRITE [#in X #in (add X c)] (silly_axiom a c).
//#REFINE refl nat (add (add (add c b) c) (add a b)).
admit

// Very trivial SSReflect example.
theorem rewriteTest8 : ∀a b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
proof
//#REFINE a => b => c => _.
//#REWRITE [#in (add (_) c)] (silly_axiom a c).
//#REFINE refl nat (add (add (add c b) c) (add a b)).
admit

theorem rewriteTest9 : ∀a b c,
  P (eq nat (add (add a b) (add c (add a b)))
            (add (add a b) (add c (add b a))))
proof
//#REFINE a => b => c => _.
//#REWRITE [(add a  _) #in X #in (add c X)] addcomm.
//#REFINE refl nat (add (add a b) (add c (add b a))).
admit

theorem rewriteTest10 : ∀a b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
proof
//#REFINE a => b => c => _.
//#REWRITE [(add a _) #in X #in (add c X)] addcomm.
//#REFINE refl nat (add (add c (add b a)) (add (add a b) (add c (add b a)))).
admit

theorem rewriteTest11 : ∀a b c,
  P (eq nat (add (add (add (add a b) c) (add (add a b) c)) (add (add a b) c))
            (add (add (add (add a b) c) (add (add b a) c)) (add (add a b) c)))
proof
//#REFINE a => b => c => _
//#REWRITE [(add a _) #in X #in (add(add _ X) _)] addcomm
//#REFINE refl nat (add (add (add (add a b) c) (add (add b a) c)) (add (add a b) c))
admit

theorem rewriteTest12 : ∀a b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
proof
//(;
//#REFINE a => b => c => _.
//#REWRITE [(add a b) #as X #in (add _ X)] addcomm.
//#REFINE refl nat (add (add c (add b a)) (add (add a b) (add c (add b a)))).
//;)
admit
