require open tests.OK.logic
require open tests.OK.bool
require open tests.OK.nat

// Symmetry of the equality (first option, rewrite).
theorem eq_sym : Πa x y, P (eq a x y) → P (eq a y x)
proof
  assume a x y h
  rewrite h
  refine refl a y
qed

// Symmetry of the equality (second option, by hand).
theorem eq_sym_other_1 : Πa x y, P (eq a x y) → P (eq a y x)
proof
  assume a x y h
  refine eqind a x y h (λz, eq a y z) (refl a y)
qed

// Symmetry of the equality (third option, by hand with a wildcard).
theorem eq_sym_other_2 : Πa x y, P (eq a x y) → P (eq a y x)
proof
  assume a x y h
  refine eqind a x y h (λz, eq a y z) _
  simpl
  refine refl a y
qed

// [s] is compatible with Leibniz equality.
theorem s_eq : Πx y, P (eq nat x y) → P (eq nat (s x) (s y))
proof
  assume x y xy
  refine eqind nat x y xy (λz, eq nat (s z) (s y)) (refl nat (s y))
qed

// [z] is right neutral for add.
theorem add0r : Πn, P (eq nat (n + 0) n)
proof
  // FIXME try to infer the predicate
  refine nat_ind (λn, eq _ (n + 0) n) ?CZ ?CS
  // Case Z
  simpl
  reflexivity
  // Case S
  assume n h
  simpl
  refine s_eq (add n 0) n h
qed

// [Π n m, n + S m = S (n+m)]
theorem add_succ_r : Πn m, P (eq nat (n + (s m)) (s (n + m)))
proof
  assume n m
  refine nat_ind (λn, eq nat (n + (s m)) (s (n + m))) ?case_0 ?case_s n
  // Case Z
  simpl
  refine refl nat (s m)
  // Case S
  simpl
  assume pn ih
  rewrite ih
  simpl
  refine refl nat (s (s (pn + m)))
qed

// Commutativity of the addition.
theorem addcomm : Πn m, P (eq nat (add n m) (add m n))
proof
  assume n m
  // FIXME try to infer nat
  refine nat_ind (λ n, eq nat (add n m) (add m n)) ?case_0 ?case_s n
  // Case Z
  simpl
  refine eq_sym _ (add m z) m (add0r m) // TODO add a symmetry tactic
  // Case S
  simpl
  assume k ih
  rewrite ih
  reflexivity
qed

// Adding the same value is the same as multiplying by 2.
theorem add_same_times_two : Πx, P (eq nat (x + x) (2 × x))
proof
  assume x
  simpl
  refine refl nat (add x x)
qed

//////////////////////////////////////////////////////////////////////////////
// Rewrite tests with quantified variables in the hypothesis.               //
//////////////////////////////////////////////////////////////////////////////

// This stupid test directly uses the addcomm lemma.
theorem rewriteTest1 : Πa b, P (eq nat (a + b) (b + a))
proof
  assume a b
  //print
  rewrite [add _ b] addcomm
  refine refl nat (add b a)
qed

// This stupid test directly uses the addcomm lemma in one place.
theorem rewriteTest2 : Πa b, P (eq nat (a + b + b) (b + a + b))
proof
  assume a b
  //print
  rewrite [x in x + b] addcomm
  refine refl nat (b + a + b)
qed

// This stupid test directly uses the addcomm lemma in two places.
theorem rewriteTest3 : Πa b,
  P (eq nat (add (add (add a b) b) (add (add a b) b))
            (add (add (add b a) b) (add (add b a) b)))
proof
  assume a b
  //print
  rewrite [x in (add x b)] addcomm
  refine refl nat (add (add (add b a) b) (add (add b a) b))
qed

// An easy contextual rewrite.
theorem rewriteTest4 : Πa b,
  P (eq nat (add (add (add a b) (add a b)) a)
            (add (add (add b a) (add a b)) a))
proof
  assume a b
  rewrite [x in (add x (add a b))] addcomm
  refine refl nat (add (add (add b a) (add a b)) a)
qed

// A slightly more complicated contextual rewrite.
theorem rewriteTest5 : Πa b,
  P (eq nat (add (add a b) (add a b)) (add (add b a) (add b a)))
proof
  assume a b
  rewrite [x in add x x] addcomm
  refine refl nat (add (add b a) (add b a))
qed

// An even more complicated rewrite, combining both wildcards and binders.
theorem rewriteTest6 : Πa b,
  P (eq nat (add (add (add a b) a) a) (add (add a (add a b)) a))
proof
  // print
  assume a b
  rewrite [x in (add x _)] addcomm
  refine refl nat (add (add a (add a b)) a)
qed

// Example 17: Very trivial SSReflect example.
symbol silly_axiom : Πm n, P (eq nat m n)

theorem rewriteTest7 : Πa b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
proof
  assume a b c
  rewrite [in x in (add x c)] (silly_axiom a c)
  refine refl nat (add (add (add c b) c) (add a b))
qed

// Very trivial SSReflect example.
theorem rewriteTest8 : Πa b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
proof
  assume a b c
  rewrite [in (add (_) c)] (silly_axiom a c)
  refine refl nat (add (add (add c b) c) (add a b))
qed

theorem rewriteTest9 : Πa b c,
  P (eq nat (add (add a b) (add c (add a b)))
            (add (add a b) (add c (add b a))))
proof
  assume a b c
  rewrite [(add a  _) in x in (add c x)] addcomm
  refine refl nat (add (add a b) (add c (add b a)))
qed

theorem rewriteTest10 : Πa b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
proof
  assume a b c
  rewrite [(add a _) in x in (add c x)] addcomm
  refine refl nat (add (add c (add b a)) (add (add a b) (add c (add b a))))
qed

theorem rewriteTest11 : Πa b c,
  P (eq nat (add (add (add (add a b) c) (add (add a b) c)) (add (add a b) c))
            (add (add (add (add a b) c) (add (add b a) c)) (add (add a b) c)))
proof
  assume a b c
  rewrite [(add a _) in x in (add (add _ x) _)] addcomm
  refine refl nat (add (add (add (add a b) c)
           (add (add b a) c)) (add (add a b) c))
qed

theorem rewriteTest12 : Πa b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
proof
  assume a b c
  rewrite [(add a b) as x in (add _ x)] addcomm
  refine refl nat (add (add c (add b a)) (add (add a b) (add c (add b a))))
qed
