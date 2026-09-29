/* Positive binary integers

by Quentin Garchery (May 2021). */

require open tests.OK.Nat tests.OK.Comp;

inductive ℙ : TYPE ≔
| I : ℙ → ℙ
| O : ℙ → ℙ
| H : ℙ;

// set code for ℙ

constant symbol pos : Set;

rule τ pos ↪ ℙ;

// boolean functions for testing head constructor

symbol isI : ℙ → 𝔹;

rule isI (I _) ↪ true
with isI (O _) ↪ false
with isI H     ↪ false;

symbol isO : ℙ → 𝔹;

rule isO (I _) ↪ false
with isO (O _) ↪ true
with isO H     ↪ false;

symbol isH : ℙ → 𝔹;

rule isH (I _) ↪ false
with isH (O _) ↪ false
with isH H     ↪ true;

// Discriminate constructors

opaque symbol I≠H [x] : π (I x ≠ H) ≔
begin
  assume x h; refine ind_eq h (λ x, istrue(isH x)) ⊤ᵢ;
end;

opaque symbol O≠H [x] : π (O x ≠ H) ≔
begin
  assume x h; refine ind_eq h (λ x, istrue(isH x)) ⊤ᵢ;
end;

opaque symbol I≠O [x y] : π (I x ≠ O y) ≔
begin
  assume x y h; refine ind_eq h (λ x, istrue(isO x)) ⊤ᵢ;
end;

opaque opaque symbol caseH x : π(x = H ∨ x ≠ H) ≔
begin
  induction
  { assume x h; apply ∨ᵢ₂; refine I≠H }
  { assume x h; apply ∨ᵢ₂; refine O≠H }
  { apply ∨ᵢ₁; reflexivity }
end;

// Constructors are injective

symbol projO : ℙ → ℙ;

rule projO (O $x) ↪ $x
with projO (I $x) ↪ I $x
with projO H ↪ H;

opaque opaque symbol O_inj p q : π(O p = O q) → π(p = q) ≔
begin
  assume p q h; apply feq projO h
end;

symbol projI : ℙ → ℙ;

rule projI (I $x) ↪ $x
with projI (O $x) ↪ O $x
with projI H ↪ H;

opaque opaque symbol I_inj p q : π(I p = I q) → π(p = q) ≔
begin
  assume p q h; apply feq projI h
end;

// Successor function

symbol succ : ℙ → ℙ;

rule succ (I $x) ↪ O (succ $x)
with succ (O $x) ↪ I $x
with succ H ↪ O H;

// Interpretation of ℙ in ℕ

symbol val : ℙ → ℕ;

rule val H ↪ 1
with val (O $x) ↪ 2 * val $x
with val (I $x) ↪ val (O $x) +1;

assert ⊢ val (O (I H)) ≡ 6;

opaque opaque symbol valS x : π(val (succ x) = val x +1) ≔
begin
  induction
  { assume x h; simplify; rewrite h; simplify; rewrite addn0; rewrite addnS; reflexivity}
  { assume x h; reflexivity }
  { reflexivity }
end;

opaque opaque symbol val_surj [n] : π(n ≠ 0 ⇒ `∃ x, val x = n) ≔
begin
  induction
  { assume h; apply ⊥ₑ; apply h; reflexivity }
  { assume n h i; apply ∨ₑ (casen n)
    { assume j; apply ∃ᵢ H; rewrite j; reflexivity }
    { assume j; apply ∃ₑ (h j); assume p k; apply ∃ᵢ (succ p);
      rewrite left k; apply valS p /*FIXME*/ } 
  }
end;

opaque opaque symbol val≠0 x : π(val x ≠ 0) ≔
begin
  induction
  { assume x h; refine s≠0 }
  { assume x h; simplify; assume i; 
    have i' :  π ((val x + (val x)) = 0)
      {rewrite left .[x in ((_ + x) = _)] addn0 (val x);
      refine i};
    apply h (∧ₑ₁ (∧ₑ₁ (addn_eq0 (val x) (val x)) i'))
  }
  { refine s≠0 }
end;

opaque opaque symbol 2*val≠0 x : π(val x + val x ≠ 0) ≔
begin
  assume x h; apply ⊥ₑ; apply val≠0 x; apply 2*=0; apply h
end;

opaque opaque symbol val_inj [x y] : π(val x = val y) → π(x = y) ≔
begin
  induction
  { assume x h; induction
    { simplify; assume y i j; rewrite h y _
        { apply 2*_inj; apply +1_inj; 
          have j' : π ((((val x + (val x + 0)) +1) = ((val y + (val y + 0)) +1)) ⇒ (((val x + val x) +1) = ((val y + val y) +1)))
            {rewrite addn0; rewrite addn0; assume h0; refine h0};
        apply (j' j) }
        { reflexivity }
    }
    { simplify; assume y i j; apply ⊥ₑ; 
      have H: π ((((val x + (val x + 0)) +1) = (val y + (val y + 0))) ⇒ (((val x + val x) +1) = (val y + val y)))
        {rewrite addn0; rewrite addn0; assume h0; refine h0};
      apply odd≠even (val x) (val y) (H j) }
    { simplify; assume i; apply ⊥ₑ; apply 2*val≠0 x; apply +1_inj; 
      have H: π ((((val x + (val x + 0)) +1) = 1) ⇒ (((val x + val x) +1) = 1))
        {rewrite addn0; assume h0; refine h0};
    apply (H i) }
  }
  { assume x h; induction
    { simplify; assume y i j; apply ⊥ₑ;
    have H: π (((val x + (val x + 0)) = ((val y + (val y + 0)) +1)) ⇒ ((val x + val x) = ((val y + val y) +1)))
        {rewrite addn0; rewrite addn0; assume h0; refine h0};
      apply odd≠even (val y) (val x) (eq_sym (H j)) }
    { simplify; assume y i j; apply feq O; apply h; apply 2*_inj; 
      have H: π (((val x + (val x + 0)) = (val y + (val y + 0))) ⇒ ((val x + val x) = (val y + val y)))
        {rewrite addn0; rewrite addn0; assume h0; refine h0};
    apply (H j) }
    { assume i; apply ⊥ₑ; apply odd≠even 0 (val x); symmetry; simplify; 
      have H: π ((val (O x) = val H) ⇒ ((val x + val x) = 1))
        {simplify val; simplify *; simplify *; simplify *; rewrite addn0; assume h0; refine h0};
    apply (H i)
    }
  }
  { induction
    { simplify; assume x h i; apply ⊥ₑ; apply val≠0 x; apply 2*=0; apply +1_inj;
      symmetry; 
      have H: π ((1 = ((val x + (val x + 0)) +1)) ⇒ (1 = ((val x + val x) +1)))
        {rewrite addn0; assume h0; refine h0};
      apply (H i) }
    { simplify; assume x h i; apply ⊥ₑ; apply odd≠even 0 (val x); simplify; 
      have H: π ((1 = (val x + (val x + 0))) ⇒ (1 = (val x + val x)))
        {rewrite addn0; assume h0; refine h0};
    apply (H i) }
    { reflexivity }
  }
end;

// ℕ-like Induction Principle

opaque symbol ind_ℙeano p : π (p H) → (Π x, π (p x) → π (p (succ x))) → Π x, π (p x) ≔
begin
  assume p pH psucc;
  have i: π(`∀ n, `∀ x, val x = n ⇒ p x) {
    induction
    { induction
      { assume x h i; apply ⊥ₑ (s≠0 i) }
      { assume x h i; apply ⊥ₑ (val≠0 (O x) i) }
      { assume i; apply ⊥ₑ (s≠0 i) }
    }
    { assume n h x; apply ∨ₑ (casen n)
      { assume i; rewrite i; assume j;
        have k: π(x = H) { apply val_inj; apply j };
        rewrite k; apply pH
      }
      { assume i; apply ∃ₑ (val_surj i); assume y j; rewrite left j;
        rewrite left valS; assume k; have l: π(x = succ y) { apply val_inj k };
        rewrite l; apply psucc y; apply h; apply j
      }
    }
  };
  assume x; apply i (val x); reflexivity
end;

// Addition of ℙ numbers with and without a carry

symbol add : ℙ → ℙ → ℙ;
symbol add_carry : ℙ → ℙ → ℙ;

rule add (I $x) (I $q) ↪ O (add_carry $x $q)
with add (I $x) (O $q) ↪ I (add $x $q)
with add (O $x) (I $q) ↪ I (add $x $q)
with add (O $x) (O $q) ↪ O (add $x $q)
with add (I $x) H      ↪ O (succ $x)
with add (O $x) H      ↪ I $x
with add H      (I $q) ↪ O (succ $q)
with add H      (O $q) ↪ I $q
with add H      H      ↪ O H;

opaque symbol addnH n : π (add n H = succ n)≔
begin
  induction
    {reflexivity}
    {reflexivity}
    {reflexivity}
end;

opaque symbol addHn n : π (add H n = succ n)≔
begin
  induction
    {reflexivity}
    {reflexivity}
    {reflexivity}
end;

rule add_carry (I $x) (I $q) ↪ I (add_carry $x $q)
with add_carry (I $x) (O $q) ↪ O (add_carry $x $q)
with add_carry (O $x) (I $q) ↪ O (add_carry $x $q)
with add_carry (O $x) (O $q) ↪ I (add $x $q)
with add_carry (I $x) H      ↪ I (succ $x)
with add_carry (O $x) H      ↪ O (succ $x)
with add_carry H      (I $q) ↪ I (succ $q)
with add_carry H      (O $q) ↪ O (succ $q)
with add_carry H      H      ↪ I H;

opaque symbol add_carryH n : π (add_carry n H = add n (O H))≔
begin
  induction
    {assume n h; simplify; rewrite addnH; reflexivity }
    {assume n h; simplify; rewrite addnH; reflexivity }
    {reflexivity}
end;

opaque symbol add_carryHn n : π (add_carry H n = add (O H) n)≔
begin
  induction
    {assume n h; simplify; rewrite addHn; reflexivity }
    {assume n h; simplify; rewrite addHn; reflexivity }
    {reflexivity}
end;

// Check that 7 + 5 = 12
assert ⊢ add (I (I H)) (I (O H)) ≡ O (O (I H));
// Check that 110101010 + 101101100 ≡ 1100010110 in base 2 (426 + 364 ≡ 790)
assert ⊢ add (O (I (O (I (O (I (O (I H))))))))
             (O (O (I (I (O (I (I (O H))))))))
  ≡ (O (I (I (O (I (O (O (O (I H)))))))));

// Interaction of succ and add

opaque symbol succ_add x y : π (succ (add x y) = add_carry x y) ≔
begin
  induction
  // case I
  { assume p prec;
    induction
      { reflexivity }
      { assume q h; simplify; rewrite prec; reflexivity }
      { rewrite addnH;  simplify; reflexivity } }
  // case O
  { assume p prec;
    induction
      { assume q h; simplify; rewrite prec; reflexivity }
      { reflexivity }
      { reflexivity } }
  // case H
  { induction { reflexivity } { reflexivity } { reflexivity }  }
end;

opaque symbol add_succ x y : π (add (succ x) y = succ (add x y)) ≔
begin
  induction
  // case I
  { assume p prec;
    induction
     { assume q h; simplify; rewrite prec; rewrite succ_add; reflexivity }
     { assume q h; simplify; rewrite prec; reflexivity }
     { reflexivity } }
  // case O
  { assume p prec;
    induction
      { assume q h; simplify; rewrite succ_add; reflexivity }
      { reflexivity }
      { reflexivity } }
  // case H
  { induction 
    { assume q h; simplify; rewrite addHn; reflexivity }
    { assume q h; simplify; rewrite addHn; reflexivity } 
    { reflexivity } }
end;

opaque symbol add_succ_right x y : π (add x (succ y) = succ (add x y)) ≔
begin
  refine ind_ℙeano (λ x, `∀ y, add x (succ y) = succ (add x y)) _ _
  // case H
  { assume n; rewrite addHn; rewrite addHn; reflexivity }
  // case succ
  { assume x xrec y;
    rewrite add_succ; rewrite add_succ; rewrite xrec; reflexivity }
end;

// Associativity of the addition

opaque symbol add_assoc x y z : π (add (add x y) z = add x (add y z)) ≔
begin
  refine ind_ℙeano (λ x, `∀ y, `∀ z, add (add x y) z = add x (add y z)) _ _
  // case H
  { assume m n; rewrite addHn; rewrite addHn; refine add_succ m n }
  // case succ
  { assume x xrec y z;
    rewrite add_succ; rewrite add_succ; rewrite add_succ;
    rewrite xrec; reflexivity }
end;

// Commutativity of the addition

opaque symbol add_com x y : π (add x y = add y x) ≔
begin
  refine ind_ℙeano (λ x, `∀ y, add x y = add y x) _ _
  // case H
  { assume n; rewrite addHn; rewrite addnH; reflexivity}
  // case succ
  { assume x xrec y;
    rewrite add_succ; rewrite add_succ_right; rewrite xrec; reflexivity }
end;

// function λ x, 2 * x - 1

symbol pos_pred_double : ℙ → ℙ;

rule pos_pred_double (I $x) ↪ I (O $x)
with pos_pred_double (O $x) ↪ I (pos_pred_double $x)
with pos_pred_double H      ↪ H;

opaque symbol pos_pred_double_succ x : π (pos_pred_double (succ x) = I x) ≔
begin
  induction
  { assume x xrec; simplify; rewrite xrec; reflexivity }
  { reflexivity }
  { reflexivity }
end;

opaque symbol succ_pos_pred_double x : π (succ (pos_pred_double x) = O x) ≔
begin
  induction
   { reflexivity }
   { assume x xrec; simplify; rewrite xrec; reflexivity }
   { reflexivity }
end;

// Comparison of ℙ numbers

symbol compare_acc : ℙ → Comp → ℙ → Comp;

rule compare_acc (I $x) $c (I $q) ↪ compare_acc $x $c $q
with compare_acc (I $x) _  (O $q) ↪ compare_acc $x Gt $q
with compare_acc (I _)  _  H      ↪ Gt
with compare_acc (O $x) _  (I $q) ↪ compare_acc $x Lt $q
with compare_acc (O $x) $c (O $q) ↪ compare_acc $x $c $q
with compare_acc (O _)  _  H      ↪ Gt
with compare_acc H      _  (I _)  ↪ Lt
with compare_acc H      _  (O _)  ↪ Lt
with compare_acc H      $c H      ↪ $c;

symbol compare x y ≔ compare_acc x Eq y;

// Commutative property of compare

opaque symbol compare_acc_com x y c :
  π (compare_acc y c x = opp (compare_acc x (opp c) y)) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
     { assume y h c; simplify; rewrite xrec; reflexivity }
     { assume y h c; simplify; rewrite xrec; reflexivity }
     { reflexivity } }
  // case O
  { assume x xrec;
    induction
     { assume y h c; simplify; rewrite xrec; reflexivity }
     { assume y h c; simplify; rewrite xrec; reflexivity }
     { reflexivity } }
  // case H
  { induction
     { reflexivity }
     { reflexivity }
     { assume c; simplify; rewrite opp_idem; reflexivity } }
end;

opaque symbol compare_com x y : π (compare y x = opp (compare x y)) ≔
begin
  assume x y; refine compare_acc_com x y Eq;
end;

// Compare decides the equality

opaque symbol compare_acc_nEq x y c : π (c ≠ Eq ⇒ compare_acc x c y ≠ Eq) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
     { assume y h c H; refine xrec y c H }
     { assume y h c H; refine xrec y Gt _; refine Gt≠Eq }
     { assume c h; refine Gt≠Eq } }
  // case O
  { assume x xrec;
    induction
     { assume y h c H; refine xrec y Lt _; refine Lt≠Eq }
     { assume y h c H; refine xrec y c H }
     { assume c h; refine Gt≠Eq } }
  // case H
  { induction
     { assume y h c H; refine Lt≠Eq }
     { assume y h c H; refine Lt≠Eq }
     { assume c Hc; refine Hc } }
end;

opaque symbol compare_decides x y : π (compare x y = Eq ⇒ x = y) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
     { assume y h H; rewrite xrec y H; reflexivity }
     { assume y h H; apply ⊥ₑ; refine compare_acc_nEq x y Gt _ H; refine Gt≠Eq }
     { assume H; apply ⊥ₑ; refine Gt≠Eq H } }
  // case O
  { assume x xrec;
    induction
     { assume y h H; apply ⊥ₑ; refine compare_acc_nEq x y Lt _ H; refine Lt≠Eq }
     { assume y h H; rewrite xrec y H; reflexivity }
     { assume H; apply ⊥ₑ; refine Gt≠Eq H } }
  // case H
  { induction
    { assume y h H; apply ⊥ₑ; refine Lt≠Eq H }
    { assume y h H; apply ⊥ₑ; refine Lt≠Eq H }
    { reflexivity } }
end;

// Compare with Gt or Lt

opaque symbol compare_Lt x y :
  π (compare_acc x Lt y = case_Comp (compare x y) Lt Lt Gt) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
     { assume y h; refine xrec y }
     { assume y h; simplify;
       refine ind_Comp (λ c, compare_acc x Gt y = c ⇒ c = case_Comp c Lt Lt Gt) _ _ _ (compare_acc x Gt y) _
         { assume H; apply ⊥ₑ; refine compare_acc_nEq x y Gt _ H }
         { refine Gt≠Eq }
         { reflexivity }
         { reflexivity } }
     { reflexivity; reflexivity } }
  // case O
  { assume x xrec;
    induction
     { assume y h; simplify;
       refine ind_Comp (λ c, compare_acc x Lt y = c ⇒ c = case_Comp c Lt Lt Gt) _ _ _ (compare_acc x Lt y) _
         { assume H; apply ⊥ₑ; refine compare_acc_nEq x y Lt _ H }
         { refine Lt≠Eq }
         { reflexivity }
         { reflexivity } }
     { reflexivity }
     { assume y h; refine xrec y;
       reflexivity } }
  // case H
  { induction { reflexivity } { reflexivity } { reflexivity } }
end;

opaque symbol compare_Gt x y :
  π (compare_acc x Gt y = case_Comp (compare x y) Gt Lt Gt) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
      { assume y h; refine xrec y }
      { assume y h; simplify;
        refine ind_Comp (λ c, compare_acc x Gt y = c ⇒ c = case_Comp c Gt Lt Gt) _ _ _ (compare_acc x Gt y) _
          { assume H; apply ⊥ₑ; refine compare_acc_nEq x y Gt _ H }
          { refine Gt≠Eq }
          { reflexivity }
          { reflexivity } }
      { reflexivity; reflexivity }  }
  // case O
  { assume x xrec;
    induction
      { assume y h; simplify;
        refine ind_Comp (λ c, compare_acc x Lt y = c ⇒ c = case_Comp c Gt Lt Gt) _ _ _ (compare_acc x Lt y) _
          { assume H; apply ⊥ₑ; refine compare_acc_nEq x y Lt _ H }
          { refine Lt≠Eq }
          { reflexivity }
          { reflexivity } }
     { reflexivity; assume y h; refine xrec y }
     { reflexivity } }
  // case H
  { induction { reflexivity } { reflexivity } { reflexivity } }
end;

// Compatibility of compare with the addition

opaque symbol compare_H_Lt y : π (compare_acc H Lt y = Lt) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol compare_Gt_H x : π (compare_acc x Gt H = Gt) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol compare_H_succ y c : π (compare_acc H c (succ y) = Lt) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol compare_succ_H x c : π (compare_acc (succ x) c H = Gt) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol compare_succ_Lt x y :
  π (compare_acc (succ x) Lt y = compare_acc x Gt y) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
     { assume y h; refine xrec y }
     { assume y h; refine xrec y }
     { reflexivity } }
  // case O
  { assume x xrec;
    induction { reflexivity } { reflexivity } { reflexivity } }
  // case H
  { induction
     { assume y h; refine compare_H_Lt y }
     { assume y h; refine compare_H_Lt y }
     { reflexivity } }
end;

opaque symbol compare_Gt_succ x y :
  π (compare_acc x Gt (succ y) = compare_acc x Lt y) ≔
begin
  assume x y;
  rewrite compare_acc_com; rewrite .[u in _ = u] compare_acc_com;
  simplify; rewrite compare_succ_Lt; reflexivity;
end;

opaque symbol compare_succ_succ x y c :
  π (compare_acc (succ x) c (succ y) = compare_acc x c y) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
     { assume y h c; refine xrec y c }
     { assume y h c; simplify; refine compare_succ_Lt x y }
     { assume c; simplify; refine compare_succ_H x c } }
  // case O
  { assume x xrec;
    induction
     { assume y h c; simplify; refine compare_Gt_succ x y }
     { assume y h c; reflexivity }
     { assume c; simplify; refine compare_Gt_H x } }
  // case H
  { induction
     { assume y h c; simplify; refine compare_H_succ y c }
     { assume y h c; simplify; refine compare_H_Lt y }
     { reflexivity } }
end;

opaque symbol compare_compat_add a x y :
  π (compare (add x a) (add y a) = compare x y) ≔
begin
  refine ind_ℙeano (λ a, `∀ x, `∀ y, compare (add x a) (add y a) = compare x y) _ _
  // case H
  { assume x y; rewrite addnH; rewrite addnH; refine compare_succ_succ x y Eq }
  // case succ
  { assume a arec x y;
    rewrite add_succ_right; rewrite add_succ_right; rewrite left arec x y;
    simplify; rewrite compare_succ_succ; reflexivity }
end;

// Multiplication

symbol mul : ℙ → ℙ → ℙ;

rule mul (I $x) $y ↪ add $y (O (mul $x $y))
with mul (O $x) $y ↪ O (mul $x $y)
with mul H      $y ↪ $y;

// enable printing of positive numbers in decimal notation

builtin "pos_one" ≔ H;
builtin "pos_double" ≔ O;
builtin "pos_succ_double" ≔ I;

// shortcuts

symbol _1 ≔ H; assert ⊢ val _1 ≡ 1;
symbol _2 ≔ O H; assert ⊢ val _2 ≡ 2;
symbol _3 ≔ I H; assert ⊢ val _3 ≡ 3;
symbol _4 ≔ O (O H); assert ⊢ val _4 ≡ 4;
symbol _5 ≔ I (O H); assert ⊢ val _5 ≡ 5;
symbol _6 ≔ O (I H); assert ⊢ val _6 ≡ 6;
symbol _7 ≔ I (I H); assert ⊢ val _7 ≡ 7;
symbol _8 ≔ O (O (O H)); assert ⊢ val _8 ≡ 8;
symbol _9 ≔ I (O (O H)); assert ⊢ val _9 ≡ 9;
symbol _10 ≔ O (I (O H)); assert ⊢ val _10 ≡ 10;
