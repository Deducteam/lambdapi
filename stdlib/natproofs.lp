require open stdlib.logic
require open stdlib.nat

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
  rewrite ih
  simpl
  refine refl nat (s (s (add pn m)))
qed

// Commutativity of the addition.
theorem addcomm : ∀n m, P (eq nat (add n m) (add m n))
proof
  intro n m
  refine nat_ind (λ (n:N), eq nat (add n m) (add m n)) ?CZ[n,m] ?CS[n,m] n
  // Case Z
  simpl
  symmetry
  refine (add0r m)
  // Case S
  simpl
  intro k ih
  rewrite ih
  rewrite add_succ_r m k
  refine refl nat (s (add m k))
qed

// Associativity of the addition.
theorem addassoc : ∀n m p, P (eq nat (add (add n m) p) (add n (add m p)))
proof
  intro n m p
  refine ((nat_ind (λ (x:N), eq nat (add (add x m) p) (add x (add m p)))
          (refl nat (add m p)) 
          _) n)
  simpl
  intro y H
  // we use the induction hypothesis
  rewrite H
  refine (refl nat (s (add y (add m p))))
qed

// Adding the same value is the same as multiplying by 2.
theorem add_same_times_two : ∀x, P (eq nat (add x x) (mul 2 x))
proof
  intro x
  simpl
  rewrite add0r
  refine refl nat (add x x)
qed

// Distributivity of the multiplication on the addition
//theorem multdist : ∀ n m p, P(eq nat (mul n (add m p))
//                                     (add (mul n m) (mul n p)))
//proof
//  intro n m p
//  refine ((nat_ind (λ (x:N), eq nat (mul x (add m p)) (add (mul x m) (mul x p)))
//          (refl nat z) 
//          _) n)
//  simpl
//  intro y H
//  rewrite H
//  print
  // Why is is not working ? Anyway FIXME and use assert
//  refine ((λ(pr:P(eq nat (add (mul y m) (mul y p))
//                         (add (mul y p) (mul y m)))), _)
//            _)
//admit