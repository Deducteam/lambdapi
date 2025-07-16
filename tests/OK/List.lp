/* Library on polymorphic lists

by Quentin Buzet (July 2022)

following https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/seq.v

seq.v documentation
-------------------

The library provides many operations. The operations are geared towards
reflection: they generally expect and provide boolean predicates.
  As there is no true subtyping, we don't use a type for non-empty
sequences; rather, we pass explicitly the head and tail of the sequence.
  The empty sequence is especially bothersome for subscripting, since it
forces us to pass a default value. This default value can often be hidden
by a notation.
  Here is the list of seq operations:
 ** Constructors:
                       seq T == the type of sequences of items of type T.
                      bitseq == seq bool.
                           □ == the empty sequence (of type T).
                       x ⸬ s == the sequence x followed by s (of type T).
                   rcons s x == the sequence s, followed by x.
All of the above, except rcons, can be used in patterns.
 ** Factories:
            nseq n x == a sequence of n x's.
         ncons n x s == a sequence of n x's, followed by s.
seqn n x_0 ... x_n-1 == the sequence of the x_i; can be partially applied.
            iota m n == the sequence m, m + 1, ..., m + n - 1.
           mkseq f n == the sequence f 0, f 1, ..., f (n - 1).
 ** Sequential access:
     head x0 s == the head (zero'th item) of s if s is non-empty, else x0.
      behead s == s minus its head, i.e., s' if s = x :: s', else □.
      last x s == the last element of x :: s (which is non-empty).
    belast x s == x :: s minus its last item.
 ** Dimensions:
        size s == the number of items (length) in s.
 ** Random access:
        nth x0 s i == the item i of s (numbered from 0), or x0 if s does
                      not have at least i+1 items (i.e., size x <= i)
              s`_i == standard notation for nth x0 s i for a default x0,
                      e.g., 0 for rings.
  set_nth x0 s i y == s where item i has been changed to y; if s does not
                      have an item i, it is first padded with copies of x0
                      to size i+1.
      incr_nth s i == the nat sequence s with item i incremented (s is
                      first padded with 0's to size i+1, if needed).
 ** Predicates:
         nilp s <=> s is □.
                := (size s == 0).
          x ∈ s == x appears in s (this requires an eqType for T).
      index x s == the first index at which x appears in s, or size s if
                   x \notin s.
        has a s <=> a holds for some item in s, where a is an applicative
                    bool predicate.
        all a s <=> a holds for all items in s.
     all2 r s t <=> the (bool) relation r holds for all _respective_ items
                   in s and t, which must also have the same size, i.e.,
                   for s := x1 ⸬ ... ⸬ x_m ⸬ □ and t := y1 ⸬ ... ⸬ y_n ⸬ □,
                   the condition [&& r x_1 y_1, ..., r x_n y_n & m == n].
       find p s == the index of the first item in s for which p holds,
                   or size s if no such item is found.
      count p s == the number of items of s for which p holds.
  count_mem x s == the multiplicity of x in s, i.e., count (pred1 x) s.
     constant s <=> all items in s are identical (trivial if s = □).
         uniq s <=> all the items in s are pairwise different.
   subseq s1 s2 <=> s1 is a subsequence of s2, i.e., s1 = mask m s2 for
                   some m : bitseq (see below).
    infix s1 s2 <=> s1 is a contiguous subsequence of s2, i.e.,
                      s ++ s1 ++ s' = s2 for some sequences s, s'.
   prefix s1 s2 <=> s1 is a subchain of s2 appearing at the beginning
                      of s2.
   suffix s1 s2 <=> s1 is a subchain of s2 appearing at the end of s2.
infix_index s1 s2 <=> the first index at which s1 appears in s2,
                      or (size s2).+1 if infix s1 s2 is false.
  perm_eq s1 s2 <=> s2 is a permutation of s1, i.e., s1 and s2 have the
                   items (with the same repetitions), but possibly in a
                   different order.
 ** Filtering:
          filter p s == the subsequence of s consisting of all the items
                        for which the (boolean) predicate p holds.
             rem x s == the subsequence of s, where the first occurrence
                        of x has been removed (compare filter (predC1 x) s
                        where ALL occurrences of x are removed).
             undup s == the subsequence of s containing only the first
                        occurrence of each item in s, i.e., s with all
                        duplicates removed.
            mask m s == the subsequence of s selected by m : bitseq, with
                        item i of s selected by bit i in m (extra items or
                        bits are ignored.
 ** Surgery:
           s1 ++ s2 == the concatenation of s1 and s2.
           take n s == the sequence containing only the first n items of s
                       (or all of s if size s <= n).
           drop n s == s minus its first n items (□ if size s <= n)
            rot n s == s rotated left n times (or s if size s <= n).
                    := drop n s ++ take n s
           rotr n s == s rotated right n times (or s if size s <= n).
              rev s == the (linear time) reversal of s.
 ** Iterators: for s == x_1 ⸬ ... ⸬ x_n ⸬ □, t == y_1 ⸬ ... ⸬ y_m ⸬ □,
       map f s == the sequence f x_1 ⸬ ... ⸬ f x_n ⸬ □.
      zip s t == itemwise pairing of s and t (dropping any extra items).
              := x_1 & y_1 ⸬ ... ⸬ x_mn & y_mn ⸬ □ with mn = minn n m.
     unzip1 s == x_1 .1 ⸬ ... ⸬ x_n .1 ⸬ □ when s : seq (S * T).
     unzip2 s == x_1 .2 ⸬ ... ⸬ x_n .2 ⸬ □ when s : seq (S * T).

Not available
-------------

       ohead s == None if s is empty, else Some x when the head of s is x.
      shape ss == the sequence of sizes of the items of the sequence of
                  sequences ss.
        'has_aP <-> the view reflect (exists2 x, x \in s & A x) (has a s),
                    where aP x : reflect (A x) (a x).
        'all_aP <=> the view for reflect {in s, forall x, A x} (all a s).
        tally s == a tally of s, i.e., a sequence of (item, multiplicity)
                   pairs for all items in sequence s (without duplicates).
incr_tally bs x == increment the multiplicity of x in the tally bs, or add
                   x with multiplicity 1 at then end if x is not in bs.
bs \is a wf_tally <=> bs is well-formed tally, with no duplicate items or
                   null multiplicities.
   tally_seq bs == the expansion of a tally bs into a sequence where each
                   (x, n) pair expands into a sequence of n x's.
 perm_eql s1 s2 <-> s1 and s2 behave identically on the left of perm_eq.
 perm_eqr s1 s2 <-> s1 and s2 behave identically on the right of perm_eq.
--> These left/right transitive versions of perm_eq make it easier to
 chain a sequence of equivalences.
  permutations s == a duplicate-free list of all permutations of s.
       catrev s1 s2 == the reversal of s1 followed by s2 (this is the
                       recursive form of rev).

 ** Dependent iterator: for s : seq S and t : S -> seq T
[seq E | x <- s, y <- t] := flatten [seq [seq E | x <- t] | y <- s]
               == the sequence of all the f x y, with x and y drawn from
                  s and t, respectively, in row-major order,
                  and where t is possibly dependent in elements of s
allpairs_dep f s t := self expanding definition for
                      [seq f x y | x <- s, y <- t y]
 ** Iterators: for s == x_1 ⸬ ... ⸬ x_n ⸬ □, t == y_1 ⸬ ... ⸬ y_m ⸬ □,
allpairs f s t := same as allpairs_dep but where t is non dependent,
                   i.e. self expanding definition for
                     [seq f x y | x <- s, y <- t]
              := f x_1 y_1 ⸬ ... ⸬ f x_1 y_m ⸬ f x_2 y_1 ⸬ ... ⸬ f x_n y_m ⸬ □
allrel r xs ys := all [pred x | all (r x) ys] xs
               <=> r x y holds whenever x is in xs and y is in ys
  all2rel r xs := allrel r xs xs
               <=> the proposition r x y holds for all possible x, y in xs.
 pairwise r xs <=> the relation r holds for any i-th and j-th element of
                   xs such that i < j.
     pmap pf s == the sequence y_i1 ⸬ ... ⸬ y_ik ⸬ □ where i1 < ... < ik,
                  pf x_i = Some y_i, and pf x_j = None iff j is not in
                  {i1, ..., ik}.
  foldr f a s == the right fold of s by f (i.e., the natural iterator).
              := f x_1 (f x_2 ... (f x_n a))
       sumn s == x_1 + (x_2 + ... + (x_n + 0)) (when s : seq nat).
  foldl f a s == the left fold of s by f.
              := f (f ... (f a x_1) ... x_n-1) x_n
  scanl f a s == the sequence of partial accumulators of foldl f a s.
              := f a x_1 ⸬ ... ⸬ foldl f a s
pairmap f a s == the sequence of f applied to consecutive items in a :: s.
              := f a x_1 ⸬ f x_1 x_2 ⸬ ... ⸬ f x_n-1 x_n ⸬ □
    flatten s == x_1 ++ ... ++ x_n when s : seq (seq T).
  reshape r s == s reshaped into a sequence of sequences whose sizes are
                 given by r (truncating if s is too long or too short).
              :=   (x_1 ⸬ ... ⸬ x_r1 ⸬ □)
                 ⸬ (x_(r1 + 1) ⸬ ... ⸬ x_(r0 + r1) ⸬ □)
                 ⸬ ...
                 ⸬ (x_(r1 + ... + r(k-1) + 1) ⸬ ... ⸬ x_(r0 + ... rk) ⸬ □)
flatten_index sh r c == the index, in flatten ss, of the item of indexes
                 (r, c) in any sequence of sequences ss of shape sh
              := sh_1 + sh_2 + ... + sh_r + c
reshape_index sh i == the index, in reshape sh s, of the sequence
                 containing the i-th item of s.
reshape_offset sh i == the offset, in the (reshape_index sh i)-th
                 sequence of reshape sh s of the i-th item of s
 ** Notation for manifest comprehensions:
        [seq x <- s | C] := filter (fun x => C) s.
        [seq E | x <- s] := map (fun x => E) s.
  [seq x <- s | C1 & C2] := [seq x <- s | C1 && C2].
    [seq E | x <- s & C] := [seq E | x <- [seq x | C]].
 --> The above allow optional type casts on the eigenvariables, as in
 [seq x : T <- s | C] or [seq E | x : T <- s, y : U <- t]. The cast may be
 needed as type inference considers E or C before s.
  We are quite systematic in providing lemmas to rewrite any composition
of two operations. "rev", whose simplifications are not natural, is
protected with nosimpl.
 ** The following are equivalent:
 [<-> P0; P1; ..; Pn] <-> P0, P1, ..., Pn are all equivalent.
                      := P0 -> P1 -> ... -> Pn -> P0
 if T : [<-> P0; P1; ..; Pn]  is such an equivalence, and i, j are in nat
 then T i j is a proof of the equivalence Pi <-> Pj between Pi and Pj;
 when i (resp. j) is out of bounds, Pi (resp. Pj) defaults to P0.
 The tactic tfae splits the goal into n+1 implications to prove.
 An example of use can be found in fingraph theorem orbitPcycle.
*/

require open tests.OK.Set tests.OK.Prop tests.OK.FOL tests.OK.Eq
  tests.OK.Nat tests.OK.Bool;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a // \Box
| ⸬ : τ a → 𝕃 a → 𝕃 a; // ::

notation ⸬ infix right 20;

// set code for 𝕃

constant symbol list : Set → Set;

rule τ (list $a) ↪ 𝕃 $a;

// is□

symbol is□ [a]: 𝕃 a → 𝔹;

rule is□ □ ↪ true
with is□ (_ ⸬ _) ↪ false;

// non confusion of constructors

opaque symbol ⸬≠□ [a] [x:τ a] [l] : π (x ⸬ l ≠ □) ≔
begin
  assume a x l h; refine ind_eq h (λ l, istrue(is□ l)) ⊤ᵢ
end;

opaque symbol □≠⸬ [a] [x:τ a] [l] : π (□ ≠ x ⸬ l) ≔
begin
  assume a x l h; apply @⸬≠□ a x l; symmetry; apply h
end;

// head

symbol head [a] : τ a → 𝕃 a → τ a;

rule head $x □ ↪ $x
with head _ ($x ⸬ _) ↪ $x;

// tail

symbol behead [a] : 𝕃 a → 𝕃 a;

rule behead □ ↪ □
with behead (_ ⸬ $l) ↪ $l;

// injectivity of constructors

opaque symbol ⸬_inj [a] [x:τ a] [l y m] : π(x ⸬ l = y ⸬ m) → π(x = y ∧ l = m) ≔
begin
  assume a x l y m e; apply ∧ᵢ { refine feq (head x) e } { refine feq behead e }
end;

// boolean equality on lists

symbol eql [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule eql _ □ □ ↪ true
with eql _ (_ ⸬ _) □ ↪ false
with eql _ □ (_ ⸬ _) ↪ false
with eql $beq ($x ⸬ $l) ($y ⸬ $m) ↪ ($beq $x $y) and (eql $beq $l $m);

opaque symbol eql_correct a (beq:τ a → τ a → 𝔹) :
  π(`∀ x, `∀ y, beq x y ⇒ x = y) → π(`∀ l, `∀ m, eql beq l m ⇒ l = m) ≔
begin
  assume a beq beq_correct; induction
  { induction
    { reflexivity }
    { simplify; assume y m i c; refine ⊥ₑ c }
  }
  { assume x l h; induction
    { simplify; assume c; refine ⊥ₑ c; }
    { simplify; assume y m i c;
      apply feq2 (⸬) _ _
      { apply beq_correct; apply @andₑ₁ _ (eql beq l m) c }
      { apply h; refine @andₑ₂ (beq x y) _ c
      } 
    }
  }
end;

opaque symbol eql_complete a (beq : τ a → τ a → 𝔹) :
  π(`∀ x, `∀ y, x = y ⇒ beq x y) → π(`∀ l, `∀ m, l = m ⇒ eql beq l m) ≔
begin
  assume a beq beq_complete; induction
  { assume m i; rewrite left i; apply ⊤ᵢ; }
  { assume x l h; induction
    { assume j; apply ⸬≠□ j; }
    { assume y m i j; simplify;
      have j': π(x = y ∧ l = m) { apply ⸬_inj j };
      apply @istrue_and (beq x y) (eql beq l m); apply ∧ᵢ
      { apply beq_complete x y; apply ∧ₑ₁ j' }
      { apply h m; apply ∧ₑ₂ j' }
    }
  }
end;

// size

symbol size [a] : 𝕃 a → ℕ;

rule size □ ↪ 0
with size (_ ⸬ $l) ↪ size $l +1;

opaque symbol size0nil [a] (l:𝕃 a) : π (size l = 0) → π (l = □) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h i; apply ⊥ₑ; apply s≠0 i; }
end;

symbol nilp [a] l ≔ is0 (@size a l);

opaque symbol size_behead [a] (l:𝕃 a) : π (size (behead l) = size l ∸1) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

// concatenation

symbol ++ [a] : 𝕃 a → 𝕃 a → 𝕃 a; notation ++ infix right 30; // \cdot

assert x y z ⊢ x ++ y ++ z ≡ x ++ (y ++ z);
assert x l m ⊢ x ⸬ l ++ m ≡ x ⸬ (l ++ m);

rule □ ++ $m ↪ $m
with ($x ⸬ $l) ++ $m ↪ $x ⸬ ($l ++ $m);

opaque symbol cat0s [a] (l:𝕃 a) : π (□ ++ l = l) ≔
begin
  reflexivity;
end;

opaque symbol cat1s [a] (x:τ a) l : π ((x ⸬ □) ++ l = (x ⸬ l)) ≔
begin
  reflexivity;
end;

opaque symbol cat_cons [a] (x:τ a) l1 l2 : π ((x ⸬ l1) ++ l2 = x ⸬ (l1 ++ l2)) ≔
begin
  reflexivity;
end;

// nseq

symbol nseq [a] : ℕ → τ a → 𝕃 a;

rule nseq 0 _ ↪ □
with nseq ($n +1) $x ↪ $x ⸬ (nseq $n $x);

// ncons

symbol ncons [a] : ℕ → τ a → 𝕃 a → 𝕃 a;

rule ncons 0 _ $l ↪ $l
with ncons ($n +1) $x $l ↪ $x ⸬ ncons $n $x $l;

opaque symbol size_ncons [a] n (x:τ a) l : π (size (ncons n x l) = n + size l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x l; simplify; apply feq (+1) (h x l); }
end;

opaque symbol size_nseq [a] n (x:τ a) : π (size (nseq n x) = n) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x; simplify; apply feq (+1) (h x); }
end;

opaque symbol cat_nseq [a] n (x:τ a) l : π (nseq n x ++ l = ncons n x l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x l; simplify; rewrite h x l; reflexivity; }
end;

opaque symbol nseqD [a] n1 n2 (x:τ a) :
  π (nseq (n1 + n2) x = nseq n1 x ++ nseq n2 x) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n1 h n2 x; simplify; rewrite h n2; reflexivity; }
end;

opaque symbol cats0 [a] (l:𝕃 a) : π(l ++ □ = l) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x ⸬ l'
    { assume x l' h; simplify; rewrite h; reflexivity; }
end;

rule $m ++ □ ↪ $m;

opaque symbol size_cat [a] (l m : 𝕃 a) : π(size (l ++ m) = size l + size m) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x⸬l'
    { assume x l' h m; simplify; rewrite h; reflexivity; }
end;

rule size ($l ++ $m) ↪ size $l + size $m;

opaque symbol catA  [a] (l m n : 𝕃 a) : π((l ++ m) ++ n = l ++ (m ++ n)) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x⸬l'
    { assume x l' h m n; simplify; rewrite h; reflexivity; }
end;

rule ($l ++ $m) ++ $n ↪ $l ++ ($m ++ $n);

opaque symbol cat_nilp [a] (l1 l2 : 𝕃 a) :
  π (nilp (l1 ++ l2) = (nilp l1 and nilp l2)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h l2; simplify; reflexivity; }
end;

// list reversal

symbol rev [a] : 𝕃 a → 𝕃 a;

rule rev □ ↪ □
with rev ($x ⸬ $l) ↪ rev $l ++ ($x ⸬ □);

opaque symbol rev_concat [a] (l m : 𝕃 a) : π(rev (l ++ m) = rev m ++ rev l) ≔
begin
  assume a;
  induction
    // case l = □
    { simplify; reflexivity; }
    // case l = ⸬
    { assume x l h m; simplify; rewrite h; reflexivity; }
end;

rule rev ($l ++ $m) ↪ rev $m ++ rev $l;

opaque symbol rev_idem [a] (l :𝕃 a) : π(rev (rev l) = l) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l h; simplify; rewrite h; reflexivity }
end;

opaque symbol size_rev [a] (l : 𝕃 a) : π(size (rev l) = size l) ≔
begin
  assume a;
  induction
    // case l = □
    { simplify; reflexivity; }
    // case l = ⸬
    { assume x l h; simplify; rewrite h; reflexivity; }
end;

// rcons

symbol rcons [a] : 𝕃 a → τ a → 𝕃 a;

rule rcons □ $x ↪ $x ⸬ □
with rcons ($e ⸬ $l) $x ↪ $e ⸬ (rcons $l $x);

opaque symbol cats1 [a] (l:𝕃 a) (z:τ a) : π (l ++ (z ⸬ □) = rcons l z) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h z; simplify; rewrite h z; reflexivity; }
end;

opaque symbol rcons_cons [a] (x:τ a) (s:𝕃 a) (z:τ a) :
  π (rcons (x ⸬ s) z = x ⸬ rcons s z) ≔
begin
  reflexivity;
end;

// Arr

symbol Arr : ℕ → Set → Set → TYPE;

rule Arr 0 _ $b ↪ τ $b
with Arr ($n +1) $a $b ↪ τ $a → Arr $n $a $b;

// seqn

symbol seqn_acc [a] n : 𝕃 a → Arr n a (list a);

rule seqn_acc 0 $l ↪ rev $l
with seqn_acc ($n +1) $l $x ↪ seqn_acc $n ($x ⸬ $l);

symbol seqn [a] n ≔ @seqn_acc a n □;

assert a (x y : τ a) ⊢ seqn 2 x y ≡ x ⸬ y ⸬ □;

// iota

symbol iota : ℕ → ℕ → 𝕃 nat;
rule iota _ 0 ↪ □
with iota $n ($k +1) ↪ $n ⸬ iota ($n +1) $k;

assert ⊢ iota 1 2 ≡ 1 ⸬ 2 ⸬ □;

// indexes

symbol indexes [a] : 𝕃 a → 𝕃 nat;

rule indexes $l ↪ iota 0 (size $l);

assert x ⊢ indexes (x ⸬ x ⸬ x  ⸬ x ⸬ □) ≡ 0 ⸬ 1 ⸬ 2 ⸬ 3 ⸬ □;

// last

symbol last [a] : τ a → 𝕃 a → τ a;

rule last $x □ ↪ $x
with last _ ($e ⸬ $l) ↪ last $e $l;

assert ⊢ last 4 (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 1;
assert ⊢ last 4 □ ≡ 4;

// belast

symbol belast [a] : τ a → 𝕃 a → 𝕃 a;

rule belast _ □ ↪ □
with belast $x ($e ⸬ $l) ↪ $x ⸬ belast $e $l;

assert ⊢ belast 4 (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 4 ⸬ 3 ⸬ 2 ⸬ □;

// nth

symbol nth [a] : τ a → 𝕃 a → ℕ → τ a;

rule nth $x □ _ ↪ $x
with nth _ ($e ⸬ _) 0 ↪ $e
with nth $x (_ ⸬ $l) ($n +1) ↪ nth $x $l $n;

assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 0 ≡ 3;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 2 ≡ 1;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 3 ≡ 4;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 42 ≡ 4;

// set_nth

symbol set_nth [a] : τ a → 𝕃 a → ℕ → τ a → 𝕃 a;

rule set_nth _ □ 0 $y ↪ $y ⸬ □
with set_nth _ (_ ⸬ $l) 0 $y ↪ $y ⸬ $l
with set_nth $x □ ($i +1) $y ↪ $x ⸬ set_nth $x □ $i $y
with set_nth $x ($e ⸬ $l) ($i +1) $y ↪ $e ⸬ set_nth $x $l $i $y;

assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 1 6 ≡ 3 ⸬ 6 ⸬ 1 ⸬ □;
assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 2 6 ≡ 3 ⸬ 2 ⸬ 6 ⸬ □;
assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 5 6 ≡ 3 ⸬ 2 ⸬ 1 ⸬ 42 ⸬ 42 ⸬ 6 ⸬ □;

// incr_nth

symbol incr_nth : 𝕃 nat → τ nat → 𝕃 nat;

rule incr_nth □ 0 ↪ 1 ⸬ □
with incr_nth □ ($i +1) ↪ 0 ⸬ incr_nth □ $i
with incr_nth ($n ⸬ $l) 0 ↪ $n +1 ⸬ $l
with incr_nth ($n ⸬ $l) ($i +1) ↪ $n ⸬ incr_nth $l $i;

assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 1 ≡ 3 ⸬ 3 ⸬ 1 ⸬ □;
assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 2 ≡ 3 ⸬ 2 ⸬ 2 ⸬ □;
assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 5 ≡ 3 ⸬ 2 ⸬ 1 ⸬ 0 ⸬ 0 ⸬ 1 ⸬ □;

// zip 

symbol zip [a b] : 𝕃 a → 𝕃 b → 𝕃 (a × b);

rule zip □ □ ↪ □
with zip □ _ ↪ □
with zip _ □ ↪ □
with zip ($x ⸬ $l) ($y ⸬ $m) ↪ $x & $y ⸬ zip $l $m;

symbol unzip1 [a b] : 𝕃 (a × b) → 𝕃 a;

rule unzip1 □  ↪ □
with unzip1 ($x & _ ⸬ $l) ↪ $x ⸬ unzip1 $l;

symbol unzip2 [a b] : 𝕃 (a × b) → 𝕃 b;

rule unzip2 □ ↪ □
with unzip2 (_ & $y ⸬ $l) ↪ $y ⸬ unzip2 $l;

assert ⊢ unzip1 ((3 & 5) ⸬ (6 & 4) ⸬ (7 & 2) ⸬ (8 & 1) ⸬ □) ≡ 3 ⸬ 6 ⸬ 7 ⸬ 8 ⸬ □;
assert ⊢ unzip2 ((3 & 5) ⸬ (6 & 4) ⸬ (7 & 2) ⸬ (8 & 1) ⸬ □) ≡ 5 ⸬ 4 ⸬ 2 ⸬ 1 ⸬ □;

symbol all2 [a b] : (τ a → τ b → 𝔹) → 𝕃 a → 𝕃 b → 𝔹;

rule all2 _ □ □ ↪ true
with all2 $p ($x ⸬ $l) ($y ⸬ $m) ↪ ($p $x $y) and (all2 $p $l $m);

opaque symbol unzip1_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size la ≤ size lb) → π (unzip1 (zip la lb) = la) ≔
begin
  assume a b; induction
  { reflexivity; }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ i; }
    { assume eb lb i j; apply feq (λ l, ea ⸬ l) (h lb j); }
  }
end;

opaque symbol unzip2_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size lb ≤ size la) → π (unzip2 (zip la lb) = lb) ≔
begin
  assume a b; induction
  { assume lb h;
     have t:π (size lb = 0) { apply ≤0 (size lb) h; };
     symmetry; apply size0nil lb t; }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i j; apply feq (λ l, eb ⸬ l) (h lb j); }
  }
end;

opaque symbol size1_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size la ≤ size lb) → π (size (zip la lb) = size la) ≔
begin
  assume a b; induction
  { reflexivity; }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ i; }
    { assume eb lb i j; apply feq (+1) (h lb j); }
  }
end;

opaque symbol size2_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size lb ≤ size la) → π (size (zip la lb) = size lb) ≔
begin
  assume a b; induction
  { assume lb h; symmetry; apply ≤0 (size lb) h; }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i j; apply feq (+1) (h lb j); }
  }
end;

opaque symbol size_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size (zip la lb) = min (size la) (size lb)) ≔
begin
  assume a b; induction
  { reflexivity }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i; simplify; apply feq (+1) (h lb); }
  }
end;

// double induction

opaque symbol seq_ind2 [a b] (p:𝕃 a → 𝕃 b → Prop) :
  π (p □ □) →
  (Π la lb ea eb, π(size la = size lb) → π(p la lb) → π(p (ea ⸬ la) (eb ⸬ lb)))
  → Π la lb, π(size la = size lb) → π(p la lb) ≔
begin
  assume a b p p0 pH; induction
  { induction
    { assume h; apply p0; }
    { assume eb lb h1 h2; apply ⊥ₑ; apply s≠0 [size lb]; symmetry; apply h2 }
  }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ (s≠0 i); }
    { assume eb lb i j;
      have t:π (size la = size lb) { apply +1_inj j; };
      apply pH la lb ea eb t (h lb t); }
  }
end;

opaque symbol zip_cat [a b] (la sa:𝕃 a) (lb sb:𝕃 b) :
  π (size la = size lb) → π (zip (la ++ sa) (lb ++ sb) = zip la lb ++ zip sa sb) ≔
begin
  assume a b la sa lb sb h;
  apply @seq_ind2 a b (λ l1 l2, (zip (l1 ++ sa) (l2 ++ sb) = zip l1 l2 ++ zip sa sb)) _ _ la lb h {
    reflexivity;
  } {
    assume l1 l2 e1 e2 h1 h2; simplify; apply feq (λ l, e1 & e2 ⸬ l) h2; 
  };
end;

opaque symbol nth_zip [a b] (x:τ a) (y:τ b) la lb i: π(size la = size lb) →
  π(nth (x & y) (zip la lb) i = nth x la i & nth y lb i) ≔
begin
  assume a b x y; induction
  { assume lb i h;
    have t: π (lb = □) { apply size0nil lb; symmetry; apply h; };
    rewrite t; reflexivity; }
  { assume ea la h; induction
    { assume i j; apply ⊥ₑ (s≠0 j); }
    { assume eb lb k; induction
      { assume m; reflexivity; }
      { assume i m n; refine h lb i _; apply +1_inj n; }
    }
  }
end;

opaque symbol rev_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size la = size lb) → π (rev (zip la lb) = zip (rev la) (rev lb)) ≔
begin
  assume a b la lb h;
  apply seq_ind2 (λ l1 l2, rev (zip l1 l2) = zip (rev l1) (rev l2)) _ _ la lb h {
    reflexivity;
  } {
    assume l1 l2 e1 e2 i j; simplify;
    have i': π(size(rev l1) = size(rev l2))
      { rewrite @size_rev; rewrite @size_rev; apply i}; 
    rewrite zip_cat (rev l1) (e1 ⸬ □) (rev l2) (e2 ⸬ □) i';
    rewrite left j; reflexivity;
  };
end;

// drop

symbol drop [a] : ℕ → 𝕃 a → 𝕃 a;

rule drop 0 $l ↪ $l
with drop _ □ ↪ □
with drop ($n +1) (_ ⸬ $l) ↪ drop $n $l;

assert ⊢ drop 3 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 1 ⸬ 41 ⸬ □;
assert ⊢ drop 10 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ □;

opaque symbol drop0 [a] (l:𝕃 a) : π (drop 0 l = l) ≔
begin
  reflexivity;
end;

opaque symbol drop_oversize [a] n (l:𝕃 a) : π (size l ≤ n) → π (drop n l = □) ≔
begin
  assume a; induction
  { assume l h; 
    have t:π (size l = 0) { apply ≤0 (size l) h;};
    simplify; apply size0nil l t;
  }
  {
    assume n h; induction
    { reflexivity; }
    { assume e l i; refine h l; }
  }
end;

opaque symbol drop_size [a] (l:𝕃 a) : π (drop (size l) l = □) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; simplify; apply h; }
end;

opaque symbol drop_cons [a] (e:τ a) l n : π (drop (n +1) (e ⸬ l) = drop n l) ≔
begin
  assume a e l n; reflexivity;
end;

opaque symbol size_drop [a] (l:𝕃 a) n : π (size (drop n l) = size l - n) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; simplify; induction
    { reflexivity; }
    { assume n i; simplify; apply h n; } 
  }
end;

opaque symbol size_cons [a] (e:τ a) n l : π (size l = n ⇔ size (e ⸬ l) = n +1) ≔
begin
  assume a e n l; apply ∧ᵢ {
    generalize n; induction
    { assume l h; simplify; rewrite h; reflexivity; }
    { assume n h l i; simplify; apply feq (+1) i;}
  } {
    generalize n; induction
    { assume l i; apply +1_inj i;}
    { assume n h l i; apply +1_inj i; }
  };
end;

opaque symbol drop_size_cat [a] n (l1 l2:𝕃 a) :
  π (size l1 = n) → π (drop n (l1 ++ l2) = l2) ≔
begin
  assume a; induction
  { assume l1 l2 h; simplify;
    have t:π (l1 = □) { apply size0nil l1 h }; rewrite t; reflexivity; }
  { assume n h; induction
    { assume l2 i; apply ⊥ₑ; apply s≠0 [n]; symmetry; apply i; }
    { assume e l1 i l2 j; apply h l1 l2; apply +1_inj j; }
  }
end;

opaque symbol drop_drop [a] (l:𝕃 a) n1 n2 :
  π (drop n1 (drop n2 l) = drop (n1 + n2) l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h n1; induction
    { reflexivity; }
    { assume n2 i; simplify; apply h n1 n2; }
  }
end;

// take

symbol take [a] : ℕ → 𝕃 a → 𝕃 a;

rule take 0 _ ↪ □
with take _ □ ↪ □
with take ($n +1) ($x ⸬ $l) ↪ $x ⸬ (take $n $l);

assert ⊢ take 3 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 7 ⸬ 2 ⸬ 3 ⸬ □;
assert ⊢ take 10 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □;

opaque symbol take0 [a] (l: 𝕃 a) : π (take 0 l = □) ≔
begin
  reflexivity;
end;

opaque symbol take_cons [a] n (x:τ a) l :
  π (take (n +1) (x ⸬ l) = (x ⸬ take n l)) ≔
begin
  assume a l; reflexivity;
end;

opaque symbol take_size [a] (l: 𝕃 a) : π (take (size l) l = l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; simplify; rewrite h; reflexivity; }
end;

opaque symbol take_oversize [a] n (l:𝕃 a) : π (size l ≤ n) → π (take n l = l) ≔
begin
  assume a; induction
  { assume l h; simplify; symmetry; apply size0nil l; apply ≤0 (size l) h; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; assume j; rewrite h l j; reflexivity; }
  }
end;

opaque symbol cat_take_drop [a] n (l:𝕃 a) : π (take n l ++ drop n l = l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; }
  }
end;

opaque symbol size_takel [a] n (l:𝕃 a) :
  π (n ≤ size l) → π (size (take n l) = n) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; induction
    { simplify; assume i; apply ⊥ₑ i; }
    { assume e l i; simplify; assume j; apply feq (+1); apply h l j; }
  }
end;

opaque symbol size_take [a] n (l:𝕃 a) :
  π (size (take n l) = if (n < size l) n (size l)) ≔
begin
abort;

opaque symbol size_take_min [a] n (l:𝕃 a) :
  π (size (take n l) = min n (size l)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; apply feq (+1) (h l); }
  }
end;

opaque symbol take_size_cat [a] n (l1 l2:𝕃 a) :
  π (size l1 = n) → π (take n (l1 ++ l2) = l1) ≔
begin
  assume a; induction
  { assume l1 l2 h; simplify; symmetry; apply size0nil l1 h; }
  { assume n h; induction
    { assume l2 i; apply ⊥ₑ; apply s≠0 [n]; symmetry; apply i; }
    { assume e1 l1 i l2 j; simplify; apply feq (λ l, e1 ⸬ l);
      apply h l1 l2; apply ∧ₑ₂ (size_cons e1 n l1) j; 
    }
  }
end;

opaque symbol takel_cat [a] (l1 l2:𝕃 a) n :
  π (n ≤ size l1) → π (take n (l1 ++ l2) = take n l1) ≔
begin
  assume a; induction
  { assume l2 n h; have t:π (n = 0) { apply ≤0 n h }; rewrite t; reflexivity; }
  { assume e1 l1 h l2; induction
    { reflexivity; }
    { assume n i j; apply feq (λ l:𝕃 a, e1 ⸬ l); apply h l2 n j; }
  }
end;

opaque symbol take_drop [a] m n (l:𝕃 a):
  π (take m (drop n l) = drop n (take (m + n) l)) ≔
begin
  assume a; induction
  { induction
    { reflexivity; }
    { assume m h; induction
      { reflexivity; }
      { assume e l i; simplify; rewrite left .[m in take m l] add0n m;
        rewrite left h l; reflexivity; }
    }
  }
  { assume n h; induction
    { reflexivity; }
    { assume m i; induction
      { reflexivity; }
      { assume e l j; refine i l; }
    }
  }
end;

opaque symbol takeD [a] m n (l:𝕃 a) :
  π (take (m + n) l = take m l ++ take n (drop m l)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume m h; induction
    { reflexivity; }
    { assume n i; induction
      { reflexivity; }
      { assume e l j; simplify; apply feq (λ l:𝕃 a, e ⸬ l);
        rewrite left addnS; apply h (n +1) l; }
    }
  }
end;

opaque symbol takeC [a] (l:𝕃 a) i j:
  π (take i (take j l) = take j (take i l)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; induction
    { reflexivity; }
    { assume i h2; induction
      { reflexivity; }
      { assume j h3; simplify; rewrite h i j; reflexivity; }
    }
  }
end;

// rot

symbol rot [a] n (l:𝕃 a) ≔ drop n l ++ take n l;

assert ⊢ rot 2 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 3 ⸬ 1 ⸬ 41 ⸬ 7 ⸬ 2 ⸬ □;

opaque symbol π_rot [a] n (l:𝕃 a) : π (drop n l ++ take n l = rot n l) ≔
begin
  reflexivity;
end;

opaque symbol rot0 [a] (l:𝕃 a) : π (rot 0 l = l) ≔
begin
  reflexivity;
end;

opaque symbol size_rot [a] (l:𝕃 a) n0 : π (size (rot n0 l) = size l) ≔
begin
  assume a l n0; simplify; rewrite addnC;
  rewrite left @size_cat a (take n0 l) (drop n0 l);
  rewrite cat_take_drop n0 l; reflexivity; 
end;

opaque symbol rot_oversize [a] n (l:𝕃 a) : π (size l ≤ n) → π (rot n l = l) ≔
begin
  assume a n l h; simplify; rewrite drop_oversize n l h;
  rewrite take_oversize n l h; reflexivity;
end;

opaque symbol rot_size [a] (l:𝕃 a) : π (rot (size l) l = l) ≔
begin
  assume a l; simplify; rewrite take_size l; rewrite @drop_size a; reflexivity;
end;

opaque symbol rot_size_cat [a] (l1 l2:𝕃 a) :
  π (rot (size l1) (l1 ++ l2) = l2 ++ l1) ≔
begin
  assume a l1 l2; simplify; 
  rewrite drop_size_cat (size l1) l1 l2 (eq_refl (size l1));
  rewrite take_size_cat (size l1) l1 l2 (eq_refl (size l1));
  reflexivity;
end;

opaque symbol take_take [a] n m :
  π (n ≤ m) → π (`∀ l:𝕃 a, take n (take m l) = take n l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; induction
    { assume i; apply ⊥ₑ i; }
    { assume m i j; induction
      { reflexivity; }
      { assume e l k; simplify; apply feq (λ l:𝕃 a, e ⸬ l) (h m j l); }
    }
  }
end;

// rotr

symbol rotr [a] n (l:𝕃 a) ≔ rot (size l - n) l;

assert ⊢ rotr 2 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 1 ⸬ 41 ⸬ 7 ⸬ 2 ⸬ 3 ⸬ □;

opaque symbol π_rotr [a] n (l:𝕃 a) :
  π (drop (size l - n) l ++ take (size l - n) l = rotr n l) ≔
begin
  reflexivity;
end;

opaque symbol rotr0 [a] (l:𝕃 a) : π (rotr 0 l = l) ≔
begin
  assume a l; simplify; rewrite take_size l; rewrite @drop_size a; reflexivity;
end;

opaque symbol rotK [a] n (l:𝕃 a) : π (rot n (rotr n l) = l) ≔
begin
abort;

opaque symbol rot_inj [a] n (l1 l2:𝕃 a) :
  π (rot n l1 = rot n l2) → π (l1 = l2) ≔
begin
abort;

// membership

symbol ∈ [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → 𝔹;

rule ∈ _ _ □ ↪ false
with ∈ $beq $x ($y ⸬ $l) ↪ $beq $x $y or ∈ $beq $x $l;

opaque symbol in_cons [a] beq (x y:τ a) l :
  π (∈ beq x (y ⸬ l) = beq x y or ∈ beq x l) ≔
begin
  assume a beq x y; induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

opaque symbol in_nil [a] beq (x:τ a) : π (∈ beq x □ = false) ≔
begin
  assume a beq x; reflexivity;
end;

opaque symbol mem_seq1 [a] beq (x y:τ a) : π (∈ beq x (y ⸬ □) = beq x y) ≔
begin
  assume a beq x y; reflexivity;
end;

opaque symbol mem_cat [a] beq (x:τ a) l1 l2 :
  π (∈ beq x (l1 ++ l2) = ∈ beq x l1 or ∈ beq x l2) ≔
begin
  assume a beq x; induction
  { reflexivity; }
  { assume e1 l1 h; simplify; assume l2; rewrite h l2; rewrite orA;
    reflexivity; }
end;

opaque symbol mem_head [a] beq (x:τ a) l :
  π (beq x x = true) → π (∈ beq x (x ⸬ l)) ≔
begin
  assume a beq x l hrefl; rewrite hrefl; apply ⊤ᵢ;
end;

opaque symbol mem_take [a] beq n l (x:τ a) :
  π (∈ beq x (take n l)) → π (∈ beq x l) ≔
begin
  assume a beq n l x h; rewrite left cat_take_drop n l;
  rewrite mem_cat beq x (take n l) (drop n l);
  refine @orᵢ₁ _ (∈ beq x (drop n l)) h;
end;

opaque symbol mem_drop [a] beq n l (x:τ a) :
  π (∈ beq x (drop n l)) → π (∈ beq x l) ≔
begin
  assume a beq n l x h; rewrite left cat_take_drop n l;
  rewrite mem_cat beq x (take n l) (drop n l);
  refine @orᵢ₂ (∈ beq x (take n l)) _ h;
end;

opaque symbol mem_rcons_left [a] beq (n m : τ a) (l : 𝕃 a) :
  π (∈ beq n l) → π (∈ beq n (rcons l m)) ≔
begin
  assume a beq n m;
  induction
    { assume h; apply ⊥ₑ h }
    { assume n0 l h1 h2;
      have H0: π (beq n n0) → π (beq n n0 or ∈ beq n (rcons l m))
        { assume h3;
          refine (orᵢ₁ (∈ beq n (rcons l m)) h3) };
          have H1: π (∈ beq n l) →  π (beq n n0 or ∈ beq n (rcons l m))
            { assume h3;
              refine (orᵢ₂ (beq n n0) (h1 h3)) };
          refine orₑ (beq n n0 or ∈ beq n (rcons l m)) h2 H0 H1 }
end;

opaque symbol 0∈indexes⸬ [a] (x : τ a) (l: 𝕃 a) :
  π (∈ eqn 0 (indexes (x ⸬ l))) ≔
begin
    assume a x;
    induction
        {refine ⊤ᵢ}
        {assume y l h;
        refine mem_rcons_left eqn 0 (size l +1) (indexes (x ⸬ l)) h }
end;

symbol +1∈iota+1 n m k :
  π (∈ eqn n (iota m k)) → π (∈ eqn (n +1) (iota (m +1) k)) ≔
begin
  assume n;
  have h: Π k m, π (∈ eqn n (iota m k)) → π (∈ eqn (n +1) (iota (m +1) k))
    { induction
      { assume m; simplify; assume h; refine h }
      { assume k h1 m; simplify; assume h2;
        refine orₑ [eqn n m] [∈ eqn n (iota (m +1) k)] (eqn n m or ∈ eqn (n +1) (iota ((m +1) +1) k)) h2 _ _
          { assume h3;
            refine orᵢ₁ (∈ eqn (n +1) (iota ((m +1) +1) k)) h3 }
          { assume h3;
            refine orᵢ₂ (eqn n m) [∈ eqn (n +1) (iota ((m +1) +1) k)] _;
            refine h1 (m +1) _; refine h3
          }
      }
    };
  assume m k; refine h k m
end;

opaque symbol +1∈indexes⸬ a (n: τ nat) (l: 𝕃 a) (y: τ a) :
  π (∈ eqn n (indexes l)) → π (∈ eqn (n +1) (indexes (y ⸬ l))) ≔
begin
  assume a n; induction
  { simplify; assume x h; refine h }
  { assume x l h y; simplify; assume i;
    refine orₑ [eqn n 0] [∈ eqn n (iota 1 (size l))] _ i _ _
      { assume j; refine orᵢ₁ (∈ eqn (n +1) (iota 2 (size l))) j }
      { assume j; refine orᵢ₂ (eqn n 0) [∈ eqn (n +1) (iota 2 (size l))] _;
        refine +1∈iota+1 n 1 (size l) j;
      }
  }
end;

// index

symbol index [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → ℕ;

rule index _ _ □ ↪ 0
with index $beq $x ($y ⸬ $l) ↪ if ($beq $x $y) 0 (index $beq $x $l +1);

assert ⊢ index eqn 2 (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ 1;
assert ⊢ index eqn 26 (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ 4;

opaque symbol index_size [a] beq (x:τ a) l : π (index beq x l ≤ size l) ≔
begin
  assume a beq x; induction
  { apply ⊤ᵢ; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ b, istrue (if b 0 (index beq x l +1) ≤ size l +1)) _ _ (beq x e) {
      apply ⊤ᵢ;
    } {
      simplify; apply h;
    };
  }
end;

opaque symbol index_head [a] beq (x:τ a) l :
  π (beq x x = true) → π (index beq x (x ⸬ l) = 0) ≔
begin
  assume a beq x l hrefl; simplify; rewrite hrefl; reflexivity;
end;

// has

symbol has [a] : (τ a → 𝔹) → 𝕃 a → 𝔹;

rule has _ □ ↪ false
with has $p ($x ⸬ $l) ↪ if ($p $x) true (has $p $l);

assert ⊢ has (λ x, eqn (x + 1) 3) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ true;
assert ⊢ has (λ x, eqn (x + 1) 3) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ false;

// all

symbol all [a] : (τ a → 𝔹) → 𝕃 a → 𝔹;

rule all _ □ ↪ true
with all $p ($x ⸬ $l) ↪ if ($p $x) (all $p $l) false;

assert ⊢ all (λ x, eqn (x + 1) 3) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ false;
assert ⊢ all (λ x, eqn (x + 1) 3) (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □) ≡ true;

// find

symbol find [a] : (τ a → 𝔹) → 𝕃 a → ℕ;

rule find _ □ ↪ 0
with find $p ($x ⸬ $l) ↪ if ($p $x) 0 (find $p $l +1);

assert ⊢ find (λ x, eqn (x + 1) 3) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ 1;
assert ⊢ find (λ x, eqn (x + 1) 3) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ 4;

opaque symbol find_size [a] (p:τ a → 𝔹) l : π (find p l ≤ size l) ≔
begin
  assume a p; induction
  { apply ⊤ᵢ; }
  { assume e l h;
    refine ind_𝔹 (λ x, istrue (if x 0 (find p l +1) ≤ size l +1)) _ _ (p e) {
      apply ⊤ᵢ;
    } {
      simplify; apply h;
    };
  }
end;

// count

symbol count [a] : (τ a → 𝔹) → 𝕃 a → ℕ;

rule count _ □ ↪ 0
with count $p ($x ⸬ $l) ↪ if ($p $x) (count $p $l +1) (count $p $l);

assert ⊢ count (λ x, eqn (x + 1) 3) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ 0;
assert ⊢ count (λ x, eqn (x + 1) 3) (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □) ≡ 4;

opaque symbol count_size [a] (p:τ a → 𝔹) l : π(count p l ≤ size l) ≔
begin
  assume a p; induction
  { apply ⊤ᵢ; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ x, istrue (if x (count p l +1) (count p l) ≤ size l +1)) _ _ (p e) {
      simplify; apply h;
    } {
      simplify;
      refine @leq_trans (count p l) (size l) (size l +1) h (leqnSn (size l)); 
    };
  }
end;

// count_mem

symbol count_mem [a] (beq : τ a → τ a → 𝔹) e ≔ count (beq e);

assert ⊢ count_mem eqn 2 (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ 0;
assert ⊢ count_mem eqn 2 (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □) ≡ 4;

// is_constant

symbol is_constant [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝔹;

rule is_constant _ □ ↪ true
with is_constant $beq ($x ⸬ $l) ↪ if (all ($beq $x) $l) true false;

assert ⊢ is_constant eqn (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □) ≡ true;
assert ⊢ is_constant eqn □ ≡ true;
assert ⊢ is_constant eqn (2 ⸬ 2 ⸬ 2 ⸬ 1 ⸬ □) ≡ false;

// uniq

symbol uniq [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝔹;

rule uniq _ □ ↪ true
with uniq $beq ($x ⸬ $l) ↪ if (not (∈ $beq $x $l)) (uniq $beq $l) false;

assert ⊢ uniq eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ true;
assert ⊢ uniq eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ false;

// subseq

symbol subseq [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule subseq _ □ □ ↪ true
with subseq _ □ (_ ⸬ _) ↪ false
with subseq _ (_ ⸬ _) □ ↪ false
with subseq $beq ($x ⸬ $l1) ($y ⸬ $l2)
     ↪ if ($beq $x $y) (subseq $beq $l1 $l2) false;

assert ⊢ subseq eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ false;
assert ⊢ subseq eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ true;

// is_prefix

symbol is_prefix [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule is_prefix _ □ _ ↪ true
with is_prefix _ (_ ⸬ _) □ ↪ false
with is_prefix $beq ($x ⸬ $l1) ($y ⸬ $l2)
     ↪ if ($beq $x $y) (is_prefix $beq $l1 $l2) false;

assert ⊢ is_prefix eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ true;

// is_suffix

symbol is_suffix [a] beq l1 l2 ≔ @is_prefix a beq (rev l1) (rev l2);

assert ⊢ is_suffix eqn (4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ true;

// is_infix

symbol is_infix [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule is_infix _ □ _ ↪ true
with is_infix _ (_ ⸬ _) □ ↪ false
with is_infix $beq ($x ⸬ $l1) ($y ⸬ $l2)
     ↪ if ($beq $x $y) (is_prefix $beq $l1 $l2) (is_infix $beq ($x ⸬ $l1) $l2);

assert ⊢ is_infix eqn (51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ true;

// infix_index

symbol infix_index [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → ℕ;

rule infix_index _ □ _ ↪ 0
with infix_index _ (_ ⸬ _) □ ↪ 0
with infix_index $beq ($x ⸬ $l1) ($y ⸬ $l2) ↪
  if ($beq $x $y)
    (if (is_prefix $beq $l1 $l2) 0 (size $l2 +1))
    (infix_index $beq ($x ⸬ $l1) $l2 +1);

assert ⊢ infix_index eqn (51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ 2;
assert ⊢ infix_index eqn (51 ⸬ 4 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ 5;

// perm_eq

symbol perm_eq [a] beq l1 l2
  ≔ @all a (λ x, eqn (count_mem beq x l1) (count_mem beq x l2)) (l1 ++ l2);

assert ⊢ perm_eq eqn (59 ⸬ 58 ⸬ 4 ⸬ 2 ⸬ □) (58 ⸬ 4 ⸬ 2 ⸬ 59 ⸬ □) ≡ true;
assert ⊢ perm_eq eqn (59 ⸬ 58 ⸬ 4 ⸬ 2 ⸬ □) (58 ⸬ 4 ⸬ 2 ⸬ 69 ⸬ □) ≡ false;

// filter

symbol filter [a] : (τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule filter _ □ ↪ □
with filter $p ($x ⸬ $l) ↪ if ($p $x) ($x ⸬ (filter $p $l)) (filter $p $l);

assert ⊢ filter (λ x, eqn (x + 1) 3) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ 2 ⸬ 68 ⸬ □) ≡ 2 ⸬ 2 ⸬ □;

symbol rmfilter [a] : (τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule rmfilter _ □ ↪ □
with rmfilter $p ($x ⸬ $l) ↪ if ($p $x) (filter $p $l) ($x ⸬ (filter $p $l));

opaque symbol size_filter [a] (p:τ a → 𝔹) l :
  π (size (filter p l) = count p l) ≔
begin
  assume a p; induction
  { reflexivity; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ x, size (if x (e ⸬ filter p l) (filter p l)) = (if x (count p l +1) (count p l))) _ _ (p e) {
      simplify; apply feq (+1) h;
    } {
      simplify; apply h;
    };
  }
end;

opaque symbol filter_cat [a] (p:τ a → 𝔹) l1 l2 :
  π (filter p (l1 ++ l2) = filter p l1 ++ filter p l2) ≔
begin
  assume a p; induction
  { reflexivity; }
  { assume e1 l1 h l2; simplify;
    refine ind_𝔹 (λ x, if x (e1 ⸬ filter p (l1 ++ l2)) (filter p (l1 ++ l2)) = if x (e1 ⸬ filter p l1) (filter p l1) ++ filter p l2) _ _ (p e1) {
      simplify; rewrite h l2; reflexivity;
    } {
      simplify; rewrite h l2; reflexivity;
    }
  }
end;

opaque symbol filter_rev [a] (p:τ a → 𝔹) l :
  π (filter p (rev l) = rev (filter p l)) ≔
begin
  assume a p; induction
  { reflexivity; }
  { assume e l h; simplify; rewrite filter_cat p (rev l) (e ⸬ □); simplify;
    refine ind_𝔹 (λ b:𝔹, (filter p (rev l) ++ (if b (e ⸬ □) □) = rev (if b (e ⸬ filter p l) (filter p l)))) _ _ (p e) {
      simplify; rewrite h; reflexivity;
    } {
      simplify; rewrite h; reflexivity;
    };
  }
end;

opaque symbol count_cat [a] (p:τ a → 𝔹) l1 l2 :
  π (count p (l1 ++ l2) = count p l1 + count p l2) ≔
begin
  assume a p l1 l2; rewrite left size_filter p l1;
  rewrite left size_filter p l2; rewrite left size_filter p (l1 ++ l2);
  rewrite filter_cat p l1 l2;
  rewrite left size_cat (filter p l1) (filter p l2); reflexivity;
end;

opaque symbol eq_find [a] beq p (l1 l2:𝕃 a) :
  π (eql beq l1 l2) → π (eqn (find p l1) (find p l2)) ≔
begin
abort;

// undup

symbol undup [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule undup _ □ ↪ □
with undup $beq ($x ⸬ $l)
  ↪ if (∈ $beq $x (undup $beq $l)) (undup $beq $l) ($x ⸬ (undup $beq $l));

assert ⊢ undup eqn (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ 2 ⸬ 3 ⸬ □) ≡ 42 ⸬ 51 ⸬ 2 ⸬ 3 ⸬ □;

opaque symbol size_undup [a] beq (l:𝕃 a) : π (size (undup beq l) ≤ size l) ≔
begin
  assume a beq; induction
  { apply ⊤ᵢ; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ x, istrue (size (if x (undup beq l) (e ⸬ undup beq l)) ≤ size l +1)) _ _ (∈ beq e (undup beq l)) {
      simplify;
      refine @leq_trans (size (undup beq l)) (size l) (size l +1) h (leqnSn (size l));
    } {
      simplify; apply h;
    };
  }
end;

opaque symbol undup_uniq [a] beq (l:𝕃 a) : π (uniq beq (undup beq l)) ≔
begin
  assume a beq; induction
  { apply ⊤ᵢ; }
  { assume e l h; simplify;
    refine ind_𝔹_eq (λ b, (istrue(uniq beq (if b (undup beq l) (e ⸬ (undup beq l)))))) (∈ beq e (undup beq l)) _ _ {
      assume i; rewrite i; simplify; apply h;
    } {
      assume i; rewrite i; simplify; rewrite i; simplify; apply h; 
    }; 
  }
end;

opaque symbol filter_undup [a] beq p (l:𝕃 a) :
  π (filter p (undup beq l) = undup beq (filter p l)) ≔
begin
abort;

opaque symbol count_undup [a] beq p (l:𝕃 a) :
  π (count p (undup beq l) ≤ count p l) ≔
begin
abort;

// map

symbol map [a b] : (τ a → τ b) → 𝕃 a → 𝕃 b;

rule map _ □ ↪ □
with map $f ($x ⸬ $l) ↪ $f $x ⸬ map $f $l;

assert ⊢ map (λ x, 3 ≤ x) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ true ⸬ false ⸬ true ⸬ true ⸬ □;

opaque symbol map_cons [a b] (f:τ a → τ b) l x :
  π (map f (x ⸬ l) = f x ⸬ map f l) ≔
begin
  assume a b f l x; reflexivity;
end;

opaque symbol map_cat [a b] (f:τ a → τ b) l1 l2 :
  π (map f (l1 ++ l2) = map f l1 ++ map f l2) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e1 l1 h l2; simplify; rewrite h l2; reflexivity; }
end;

opaque symbol size_map [a b] (f:τ a → τ b) l : π (size (map f l) = size l) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h; simplify; apply feq (+1) h; }
end;

opaque symbol behead_map [a b] (f:τ a → τ b) l :
  π (behead (map f l) = map f (behead l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

opaque symbol map_rcons [a b] (f:τ a → τ b) l e :
  π (map f (rcons l e) = rcons (map f l) (f e)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume x l h e; simplify; rewrite h e; reflexivity; }
end;

opaque symbol last_map [a b] (f:τ a → τ b) l x :
  π (last (f x) (map f l) = f (last x l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h x; simplify; rewrite h e; reflexivity; }
end;

opaque symbol belast_map [a b] (f:τ a → τ b) l x :
  π (belast (f x) (map f l) = map f (belast x l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h x; simplify; rewrite h e; reflexivity; }
end;

opaque symbol map_take [a b] (f:τ a → τ b) n l :
  π (map f (take n l) = take n (map f l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; } 
  }
end;

opaque symbol map_drop [a b] (f:τ a → τ b) n l :
  π (map f (drop n l) = drop n (map f l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; } 
  }
end;

opaque symbol map_rot [a b] (f:τ a → τ b) n l :
  π (map f (rot n l) = rot n (map f l)) ≔
begin
  assume a b f n l; simplify; rewrite map_cat f (drop n l) (take n l);
  rewrite map_take f n l; rewrite map_drop f n l; reflexivity; 
end;

opaque symbol map_rotr [a b] (f:τ a → τ b) n l :
  π (map f (rotr n l) = rotr n (map f l)) ≔
begin
  assume a b f n l; simplify;
  rewrite map_cat f (drop (size l - n) l) (take (size l - n) l);
  rewrite map_drop f (size l - n) l; rewrite map_take f (size l - n) l;
  rewrite size_map f l; reflexivity;
end;

opaque symbol map_rev [a b] (f:τ a → τ b) l :
  π (map f (rev l) = rev (map f l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h; simplify; rewrite map_cat f (rev l) (e ⸬ □); rewrite h;
    reflexivity; }
end;

opaque symbol inj_map [a b] (f:τ a → τ b) :
  (Π x y, π(f x = f y) → π(x = y)) →
  Π l1 l2, π (map f l1 = map f l2) → π (l1 = l2) ≔
begin
  assume a b f h; induction
  { induction
    { reflexivity; }
    { simplify; assume e l i j; apply ⊥ₑ (□≠⸬ j) }
  }
  { assume e1 l1 i; induction
    { assume j; apply ⊥ₑ (⸬≠□ j) }
    {
      simplify; assume e2 l2 j k; apply feq2 (⸬) _ _
      { apply h; apply ∧ₑ₁ (⸬_inj k) }
      { apply i; apply ∧ₑ₂ (⸬_inj k) }
    }
  }
end;

// sumn

symbol sumn : 𝕃 nat → ℕ;

rule sumn □ ↪ 0
with sumn ($x ⸬ $l) ↪ $x + sumn $l;

assert ⊢ sumn (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 6;

// prodn

symbol prodn : 𝕃 nat → ℕ;

rule prodn □ ↪ 1
with prodn ($x ⸬ $l) ↪ $x * prodn $l;

assert ⊢ prodn (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 3 !;
