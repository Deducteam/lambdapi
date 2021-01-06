require open tests.OK.logic;
require open tests.OK.bool;
require open tests.OK.nat;

// Symmetry of the equality (first option, rewrite).
opaque symbol eq_sym : Π a x y, P (eq a x y) → P (eq a y x)
≔ begin
  assume a x y h
  rewrite h
  refine refl a y
end

// Symmetry of the equality (second option, by hand).
opaque symbol eq_sym_other_1 : Π a x y, P (eq a x y) → P (eq a y x)
≔ begin
  assume a x y h
  refine eqind a x y h (λ z, eq a y z) (refl a y)
end

// Symmetry of the equality (third option, by hand with a wildcard).
opaque symbol eq_sym_other_2 : Π a x y, P (eq a x y) → P (eq a y x)
≔ begin
  assume a x y h
  refine eqind a x y h (λ z, eq a y z) _
  simpl
  refine refl a y
end

// [s] is compatible with Leibniz equality.
opaque symbol s_eq : Π x y, P (eq nat x y) → P (eq nat (s x) (s y))
≔ begin
  assume x y xy
  refine eqind nat x y xy (λ z, eq nat (s z) (s y)) (refl nat (s y))
end

// [z] is right neutral for add.
opaque symbol add0r : Π n, P (eq nat (n + 0) n)
≔ begin
  // FIXME try to infer the predicate
  refine nat_ind (λ n, eq _ (n + 0) n) ?CZ ?CS
  // Case Z
  simpl
  reflexivity
  // Case S
  assume n h
  simpl
  refine s_eq (add n 0) n h
end

// [Π n m, n + S m = S (n+m)]
opaque symbol add_succ_r : Π n m, P (eq nat (n + (s m)) (s (n + m)))
≔ begin
  assume n m
  refine nat_ind (λ n, eq nat (n + (s m)) (s (n + m))) ?case_0 ?case_s n
  // Case Z
  simpl
  refine refl nat (s m)
  // Case S
  simpl
  assume pn ih
  rewrite ih
  simpl
  refine refl nat (s (s (pn + m)))
end

// Commutativity of the addition.
opaque symbol addcomm : Π n m, P (eq nat (add n m) (add m n))
≔ begin
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
end

// Adding the same value is the same as multiplying by 2.
opaque symbol add_same_times_two : Π x, P (eq nat (x + x) (2 × x))
≔ begin
  assume x
  simpl
  refine refl nat (add x x)
end

//////////////////////////////////////////////////////////////////////////////
// Rewrite tests with quantified variables in the hypothesis.               //
//////////////////////////////////////////////////////////////////////////////

// This stupid test directly uses the addcomm lemma.
opaque symbol rewriteTest1 : Π a b, P (eq nat (a + b) (b + a))
≔ begin
  assume a b
  //print
  rewrite [add _ b] addcomm
  refine refl nat (add b a)
end

// This stupid test directly uses the addcomm lemma in one place.
opaque symbol rewriteTest2 : Π a b, P (eq nat (a + b + b) (b + a + b))
≔ begin
  assume a b
  //print
  rewrite [x in x + b] addcomm
  refine refl nat (b + a + b)
end

// This stupid test directly uses the addcomm lemma in two places.
opaque symbol rewriteTest3 : Π a b,
  P (eq nat (add (add (add a b) b) (add (add a b) b))
            (add (add (add b a) b) (add (add b a) b)))
≔ begin
  assume a b
  //print
  rewrite [x in (add x b)] addcomm
  refine refl nat (add (add (add b a) b) (add (add b a) b))
end

// An easy contextual rewrite.
opaque symbol rewriteTest4 : Π a b,
  P (eq nat (add (add (add a b) (add a b)) a)
            (add (add (add b a) (add a b)) a))
≔ begin
  assume a b
  rewrite [x in (add x (add a b))] addcomm
  refine refl nat (add (add (add b a) (add a b)) a)
end

// A slightly more complicated contextual rewrite.
opaque symbol rewriteTest5 : Π a b,
  P (eq nat (add (add a b) (add a b)) (add (add b a) (add b a)))
≔ begin
  assume a b
  rewrite [x in add x x] addcomm
  refine refl nat (add (add b a) (add b a))
end

// An even more complicated rewrite, combining both wildcards and binders.
opaque symbol rewriteTest6 : Π a b,
  P (eq nat (add (add (add a b) a) a) (add (add a (add a b)) a))
≔ begin
  // print
  assume a b
  rewrite [x in (add x _)] addcomm
  refine refl nat (add (add a (add a b)) a)
end

// Example 17: Very trivial SSReflect example.
symbol silly_axiom : Π m n, P (eq nat m n);

opaque symbol rewriteTest7 : Π a b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
≔ begin
  assume a b c
  rewrite [in x in (add x c)] (silly_axiom a c)
  refine refl nat (add (add (add c b) c) (add a b))
end

// Very trivial SSReflect example.
opaque symbol rewriteTest8 : Π a b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
≔ begin
  assume a b c
  rewrite [in (add (_) c)] (silly_axiom a c)
  refine refl nat (add (add (add c b) c) (add a b))
end

opaque symbol rewriteTest9 : Π a b c,
  P (eq nat (add (add a b) (add c (add a b)))
            (add (add a b) (add c (add b a))))
≔ begin
  assume a b c
  rewrite [(add a  _) in x in (add c x)] addcomm
  refine refl nat (add (add a b) (add c (add b a)))
end

opaque symbol rewriteTest10 : Π a b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
≔ begin
  assume a b c
  rewrite [(add a _) in x in (add c x)] addcomm
  refine refl nat (add (add c (add b a)) (add (add a b) (add c (add b a))))
end

opaque symbol rewriteTest11 : Π a b c,
  P (eq nat (add (add (add (add a b) c) (add (add a b) c)) (add (add a b) c))
            (add (add (add (add a b) c) (add (add b a) c)) (add (add a b) c)))
≔ begin
  assume a b c
  rewrite [(add a _) in x in (add (add _ x) _)] addcomm
  refine refl nat (add (add (add (add a b) c)
           (add (add b a) c)) (add (add a b) c))
end

opaque symbol rewriteTest12 : Π a b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
≔ begin
  assume a b c
  rewrite [(add a b) as x in (add _ x)] addcomm
  refine refl nat (add (add c (add b a)) (add (add a b) (add c (add b a))))
end
