require open tests.OK.logic;
require open tests.OK.bool;
require open tests.OK.nat;

rule T nat ↪ N;

// Symmetry of the equality (first option, rewrite).
opaque symbol eq_sym a (x y:T a) : P (x = y) → P (y = x)
≔ begin
  assume a x y h;
  rewrite h;
  refine refl a y;
end;

// Symmetry of the equality (second option, by hand).
opaque symbol eq_sym_other_1 a (x y:T a) : P (x = y) → P (y = x)
≔ begin
  assume a x y h;
  refine eqind a x y h (λ z, y = z) (refl a y);
end;

// Symmetry of the equality (third option, by hand with a wildcard).
opaque symbol eq_sym_other_2 a (x y:T a) : P (x = y) → P (y = x)
≔ begin
  assume a x y h;
  refine eqind a x y h (λ z, y = z) _;
  simplify;
  refine refl a y;
end;

// [s] is compatible with Leibniz equality.
opaque symbol s_eq x y : P (x = y) → P (s x = s y)
≔ begin
  assume x y xy;
  refine eqind nat x y xy (λ z, s z = s y) (refl nat (s y));
end;

// [z] is right neutral for add.
opaque symbol add0r n : P (n + 0 = n)
≔ begin
  // FIXME try to infer the predicate
  refine nat_ind (λ n, n + 0 = n) ?CZ ?CS;
  // Case Z
  simplify;
  reflexivity;
  // Case S
  assume n h;
  simplify;
  refine s_eq (n + 0) n h;
end;

// [Π n m, n + S m = S (n+m)]
opaque symbol add_succ_r n m : P (n + (s m) = s (n + m))
≔ begin
  assume n m;
  refine nat_ind (λ n, n + (s m) = s (n + m)) ?case_0 ?case_s n;
  // Case Z
  simplify;
  refine refl nat (s m);
  // Case S
  simplify;
  assume pn ih;
  rewrite ih;
  simplify;
  refine refl nat (s (s (pn + m)));
end;

// Commutativity of the addition.
opaque symbol addcomm n m : P (n + m = m + n)
≔ begin
  assume n m;
  // FIXME try to infer nat
  refine nat_ind (λ n, n + m = m + n) ?case_0 ?case_s n;
  // Case Z
  simplify;
  refine eq_sym _ (m + z) m (add0r m); // TODO add a symmetry tactic
  // Case S
  simplify;
  assume k ih;
  rewrite ih;
  reflexivity;
end;

// Adding the same value is the same as multiplying by 2.
opaque symbol add_same_times_two x : P (x + x = 2 × x)
≔ begin
  assume x;
  simplify;
  refine refl nat (x + x);
end;

//////////////////////////////////////////////////////////////////////////////
// Rewrite tests with quantified variables in the hypothesis.               //
//////////////////////////////////////////////////////////////////////////////

// This stupid test directly uses the addcomm lemma.
opaque symbol rewriteTest1 a b : P (a + b = b + a)
≔ begin
  assume a b;
  rewrite [_ + b] addcomm;
  refine refl nat (b + a);
end;

// This stupid test directly uses the addcomm lemma in one place.
opaque symbol rewriteTest2 a b : P (a + b + b = b + a + b)
≔ begin
  assume a b;
  rewrite [x in x + b] addcomm;
  refine refl nat (b + a + b);
end;

// This stupid test directly uses the addcomm lemma in two places.
opaque symbol rewriteTest3 a b :
  P (((a + b) + b) + ((a + b) + b) = ((b + a) + b) + ((b + a) + b))
≔ begin
  assume a b;
  rewrite [x in (x + b)] addcomm;
  refine refl nat (((b + a) + b) + ((b + a) + b));
end;

// An easy contextual rewrite.
opaque symbol rewriteTest4 a b :
  P (((a + b) + (a + b)) + a = ((b + a) + (a + b)) + a)
≔ begin
  assume a b;
  rewrite [x in (x + (a + b))] addcomm;
  refine refl nat (((b + a) + (a + b)) + a);
end;

// A slightly more complicated contextual rewrite.
opaque symbol rewriteTest5 a b : P ((a + b) + (a + b) = (b + a) + (b + a))
≔ begin
  assume a b;
  rewrite [x in x + x] addcomm;
  refine refl nat ((b + a) + (b + a));
end;

// An even more complicated rewrite, combining both wildcards and binders.
opaque symbol rewriteTest6 a b : P (((a + b) + a) + a = (a + (a + b)) + a)
≔ begin
  assume a b;
  rewrite [x in (x + _)] addcomm;
  refine refl nat ((a + (a + b)) + a);
end;

// Example 17: Very trivial SSReflect example.
symbol silly_axiom (m n:N) : P (m = n);

opaque symbol rewriteTest7 a b c :
 P (((a + b) + c) + (a + b) = ((c + b) + c) + (a + b))
≔ begin
  assume a b c;
  rewrite [in x in (x + c)] (silly_axiom a c);
  refine refl nat (((c + b) + c) + (a + b));
end;

// Very trivial SSReflect example.
opaque symbol rewriteTest8 a b c :
 P (((a + b) + c) + (a + b) = ((c + b) + c) + (a + b))
≔ begin
  assume a b c;
  rewrite [in (_ + c)] (silly_axiom a c);
  refine refl nat (((c + b) + c) + (a + b));
end;

opaque symbol rewriteTest9 a b c :
  P ((a + b) + (c + (a + b)) = (a + b) + (c + (b + a)))
≔ begin
  assume a b c;
  rewrite [a + _ in x in c + x] addcomm;
  refine refl nat ((a + b) + (c + (b + a)));
end;

opaque symbol rewriteTest10 a b c :
  P ((c + (a + b)) + ((a + b) + (c + (a + b)))
     = (c + (b + a)) + ((a + b) + (c + (b + a))))
≔ begin
  assume a b c;
  rewrite [a + _ in x in c + x] addcomm;
  refine refl nat ((c + (b + a)) + ((a + b) + (c + (b + a))));
end;

opaque symbol rewriteTest11 a b c :
  P ((((a + b) + c) + ((a + b) + c)) + ((a + b) + c)
    = (((a + b) + c) + ((b + a) + c)) + ((a + b) + c))
≔ begin
  assume a b c;
  rewrite [a + _ in x in (_ + x) + _] addcomm;
  refine refl nat ((((a + b) + c) + ((b + a) + c)) + ((a + b) + c));
end;

opaque symbol rewriteTest12 a b c :
  P ((c + (a + b)) + ((a + b) + (c + (a + b)))
    = (c + (b + a)) + ((a + b) + (c + (b + a))))
≔ begin
  assume a b c;
  rewrite [(a + b) as x in _ + x] addcomm;
  refine refl nat ((c + (b + a)) + ((a + b) + (c + (b + a))));
end;
