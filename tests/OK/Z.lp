/* Binary integers

by Quentin Garchery (May 2021). */

require open tests.OK.Pos;

inductive ℤ : TYPE ≔ // \BbbZ
| Z0 : ℤ
| Zpos : ℙ → ℤ
| Zneg : ℙ → ℤ;

// set code for ℤ

constant symbol int : Set;

rule τ int ↪ ℤ;

// boolean functions for testing head constructor

symbol isZ0 : ℤ → 𝔹;

rule isZ0 Z0       ↪ true
with isZ0 (Zpos _) ↪ false
with isZ0 (Zneg _) ↪ false;

symbol isZpos : ℤ → 𝔹;

rule isZpos Z0       ↪ false
with isZpos (Zpos _) ↪ true
with isZpos (Zneg _) ↪ false;

symbol isZneg : ℤ → 𝔹;

rule isZneg Z0       ↪ false
with isZneg (Zpos _) ↪ false
with isZneg (Zneg _) ↪ true;

// Discriminate constructors

opaque symbol Zpos≠Z0 p : π (Zpos p ≠ Z0) ≔
begin
  assume n h; refine ind_eq h (λ n, istrue(isZ0 n)) ⊤ᵢ
end;

opaque symbol Zneg≠Z0 p : π (Zneg p ≠ Z0) ≔
begin
  assume n h; refine ind_eq h (λ n, istrue(isZ0 n)) ⊤ᵢ
end;

opaque symbol Zpos≠Zneg p q : π (Zpos p ≠ Zneg q) ≔
begin
  assume x y h; refine ind_eq h (λ n, istrue(isZneg n)) ⊤ᵢ
end;

// Unary opposite

symbol — : ℤ → ℤ;
notation — prefix 24;

rule — Z0 ↪ Z0
with — (Zpos $p) ↪ Zneg $p
with — (Zneg $p) ↪ Zpos $p;

symbol —_idem z : π (— — z = z) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

// Doubling functions

symbol double : ℤ → ℤ;

rule double Z0 ↪ Z0
with double (Zpos $p) ↪ Zpos (O $p)
with double (Zneg $p) ↪ Zneg (O $p);

symbol succ_double : ℤ → ℤ;

rule succ_double Z0 ↪ Zpos H
with succ_double (Zpos $p) ↪ Zpos (I $p)
with succ_double (Zneg $p) ↪ Zneg (pos_pred_double $p);

symbol pred_double : ℤ → ℤ;

rule pred_double Z0 ↪ Zneg H
with pred_double (Zpos $p) ↪ Zpos (pos_pred_double $p)
with pred_double (Zneg $p) ↪ Zneg (I $p);

// Interaction of opp and doubling functions

opaque symbol double_opp z : π (double (— z) = — double z) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol succ_double_opp z : π (succ_double (— z) = — pred_double z) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol pred_double_opp z : π (pred_double (— z) = — succ_double z) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

// Binary negation on ℙ

symbol sub : ℙ → ℙ → ℤ;

rule sub (I $p) (I $q) ↪ double (sub $p $q)
with sub (I $p) (O $q) ↪ succ_double (sub $p $q)
with sub (I $p) H      ↪ Zpos (O $p)
with sub (O $p) (I $q) ↪ pred_double (sub $p $q)
with sub (O $p) (O $q) ↪ double (sub $p $q)
with sub (O $p) H      ↪ Zpos (pos_pred_double $p)
with sub H      (I $q) ↪ Zneg (O $q)
with sub H      (O $q) ↪ Zneg (pos_pred_double $q)
with sub H       H     ↪ Z0;

opaque symbol sub_same z : π (sub z z = Z0) ≔
begin
  induction
   { assume x xrec; simplify; rewrite xrec; reflexivity }
   { assume x xrec; simplify; rewrite xrec; reflexivity }
   { reflexivity }
end;

opaque symbol sub_opp x y : π (— sub x y = sub y x) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
     { assume y h; simplify; rewrite left xrec y; rewrite double_opp; reflexivity }
     { assume y h; simplify; rewrite left xrec y; rewrite pred_double_opp; reflexivity }
     { reflexivity } }
  // case O
  { assume x xrec;
    induction
     { assume y h; simplify; rewrite left xrec y; rewrite succ_double_opp; reflexivity }
     { assume y h; simplify; rewrite left xrec y; rewrite double_opp; reflexivity }
     { reflexivity } }
  // case H
  { induction { reflexivity } { reflexivity } { reflexivity } }
end;

// Addition of integers

symbol + : ℤ → ℤ → ℤ;
notation + infix right 20;

rule Z0      + $y      ↪ $y
with Zpos $x + Z0      ↪ Zpos $x
with Zneg $x + Z0      ↪ Zneg $x
with Zpos $x + Zpos $y ↪ Zpos (add $x $y)
with Zpos $x + Zneg $y ↪ sub $x $y
with Zneg $x + Zpos $y ↪ sub $y $x
with Zneg $x + Zneg $y ↪ Zneg (add $x $y);

opaque symbol +Z0 x : π (x + Z0 = x) ≔
begin
  induction
    {reflexivity}
    {reflexivity}
    {reflexivity} 
end;

// Interaction of addition with opposite

opaque symbol distr_—_+ x y : π (— (x + y) = — x + — y) ≔
begin
  induction
  // case Z0
  { reflexivity }
  // case Zpos
  { assume x;
    induction
     { reflexivity }
     { reflexivity }
     { assume y; simplify; rewrite sub_opp; reflexivity } }
  // case Zneg
  { assume x;
    induction
      { reflexivity }
      { assume y; simplify; rewrite sub_opp; reflexivity }
      { reflexivity } }
end;

// Commutativity of addition

opaque symbol +_com x y : π (x + y = y + x) ≔
begin
  induction
  // case Z0
  { induction { reflexivity } { reflexivity } { reflexivity } }
  // case Zpos
  { assume x;
    induction
     { reflexivity }
     { assume y; simplify; rewrite add_com; reflexivity }
     { reflexivity } }
  // case Zneg
  { assume x;
    induction
     { reflexivity }
     { reflexivity }
     { assume y; simplify; rewrite add_com; reflexivity } }
end;

// Interaction of succ and doubling functions

opaque symbol pred_double_succ x : π (pred_double (x + Zpos H) = succ_double x) ≔
begin
  induction
   { reflexivity }
   { assume x; simplify; rewrite addnH; rewrite pos_pred_double_succ; reflexivity }
   { induction { reflexivity } { reflexivity } { reflexivity } }
end;

opaque symbol succ_pred_double x : π (pred_double x + Zpos H = double x) ≔
begin
  induction
   { reflexivity }
   { assume x; simplify; rewrite addnH; rewrite succ_pos_pred_double; reflexivity }
   { reflexivity }
end;

opaque symbol succ_double_carac x : π (succ_double x = double x + Zpos H) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol double_succ x : π (double (x + Zpos H) = succ_double x + Zpos H) ≔
begin
  induction
   { reflexivity }
   { assume n; simplify; rewrite addnH; reflexivity }
   { induction { reflexivity } { reflexivity } { reflexivity } }
end;

// Negation

symbol - x y ≔ x + — y;

notation - infix left 20;

opaque symbol -_same z : π (z + — z = Z0) ≔
begin
  induction
   { reflexivity }
   { simplify; refine sub_same }
   { simplify; refine sub_same }
end;

// Associativity

opaque symbol sub_succ x y : π (sub (succ x) y = sub x y + Zpos H) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
      { assume y h; simplify; rewrite xrec; rewrite pred_double_succ;
        rewrite succ_double_carac; reflexivity }
      { assume y h; simplify; rewrite xrec; rewrite double_succ; reflexivity }
      { simplify; rewrite pos_pred_double_succ; reflexivity } }
  // case O
  { assume x xrec;
    induction
      { assume y h; simplify; rewrite left succ_pred_double; reflexivity }
      { assume y h; simplify; rewrite succ_double_carac; reflexivity }
      { simplify; rewrite addnH; rewrite succ_pos_pred_double; reflexivity } }
  // case H
  { induction
     { induction { reflexivity } { reflexivity } { reflexivity } }
     { induction { reflexivity } { reflexivity } { reflexivity } }
     { reflexivity } }
end;

opaque symbol add_Zpos_succ x p : π (x + Zpos (succ p) = (x + Zpos p) + Zpos H) ≔
begin
  induction
   { assume n; simplify; rewrite addnH; reflexivity}
   { assume x p; simplify; rewrite add_succ_right; rewrite addnH; reflexivity }
   { assume x p; simplify; rewrite sub_succ; reflexivity }
end;

opaque symbol sub_add_Zpos a b c : π (sub a b + Zpos c = sub (add a c) b) ≔
begin
  assume a b c;
  refine ind_ℙeano (λ c, sub a b + Zpos c = sub (add a c) b) _ _ c
  // case H
  { simplify; rewrite addnH; rewrite sub_succ; reflexivity }
  // case succ
  { assume r rrec; rewrite add_Zpos_succ; rewrite rrec;
    rewrite add_succ_right; rewrite sub_succ; reflexivity }
end;

opaque symbol sub_add_Zneg a b c : π (sub a b + Zneg c = sub a (add b c)) ≔
begin
  assume a b c;
  rewrite left sub_opp (add b c) a;
  rewrite left sub_add_Zpos;
  rewrite distr_—_+; rewrite sub_opp; reflexivity;
end;

opaque symbol +_assoc x y z : π ((x + y) + z = x + (y + z)) ≔
begin
  induction
  { reflexivity }
  { assume x;
    induction
     { reflexivity }
     { assume y;
       induction
         { reflexivity }
         // case Zpos - Zpos - Zpos
         { assume z; simplify; rewrite add_assoc; reflexivity }
         // case Zpos - Zpos - Zneg
         { assume z; simplify; rewrite +_com; rewrite sub_add_Zpos;
           rewrite add_com; reflexivity } }

     { assume y;
       induction
         { rewrite +Z0; rewrite +Z0; reflexivity}
         // case Zpos - Zneg - Zpos
         { assume z; simplify; rewrite sub_add_Zpos; rewrite +_com;
           rewrite sub_add_Zpos; rewrite add_com; reflexivity }
         // case Zpos - Zneg - Zneg
         { assume z; simplify; rewrite sub_add_Zneg; reflexivity } } }

  { assume x;
    induction
      { reflexivity }
      { assume y;
        induction
          { simplify; rewrite +Z0; reflexivity }
          // case Zneg - Zpos - Zpos
          { assume z; simplify; rewrite sub_add_Zpos; reflexivity }
          // case Zneg - Zpos - Zneg
          { assume z; simplify; rewrite sub_add_Zneg; rewrite +_com;
            rewrite sub_add_Zneg; rewrite add_com; reflexivity } }

      { assume y;
        induction
          { reflexivity }
          // case Zneg - Zneg - Zpos
          { assume z; simplify; rewrite +_com; rewrite sub_add_Zneg;
            rewrite add_com; reflexivity }
          // case Zneg - Zneg - Zneg
          { assume z; simplify; rewrite add_assoc; reflexivity } } }
end;

// Comparison of integers

require open tests.OK.Comp;

symbol ≐ : ℤ → ℤ → Comp; notation ≐ infix 12; // \doteq

rule Z0      ≐ Z0      ↪ Eq
with Z0      ≐ Zpos _  ↪ Lt
with Z0      ≐ Zneg _  ↪ Gt
with Zpos _  ≐ Z0      ↪ Gt
with Zpos $p ≐ Zpos $q ↪ compare $p $q
with Zpos _  ≐ Zneg _  ↪ Gt
with Zneg _  ≐ Z0      ↪ Lt
with Zneg _  ≐ Zpos _  ↪ Lt
with Zneg $p ≐ Zneg $q ↪ opp (compare $p $q);

symbol Zneg≐ p q : π ((Zneg p ≐ Zneg q) = compare q p) ≔
begin
  assume p q; rewrite compare_com; reflexivity
end;

// ≐ decides the equality of integers

opaque symbol ≐_decides x y : π (x ≐ y = Eq ⇒ x = y) ≔
begin
  induction
  // case Z0
  { induction
      { reflexivity }
      { assume y H; apply ⊥ₑ; refine Lt≠Eq H }
      { assume y H; apply ⊥ₑ; refine Gt≠Eq H } }
  // case Zpos
  { assume x;
    induction
     { assume H; apply ⊥ₑ; refine Gt≠Eq H }
     { assume y H; rewrite compare_decides x y H; reflexivity }
     { assume y H; apply ⊥ₑ; refine Gt≠Eq H } }
  // case Zneg
  { assume x;
    induction
     { assume H; apply ⊥ₑ; refine Lt≠Eq H }
     { assume y H; apply ⊥ₑ; refine Lt≠Eq H }
     { assume y H;
       have H' : π (compare y x = Eq)
       { refine ind_eq (eq_sym (Zneg≐ x y)) (λ c, c = Eq) H };
       rewrite compare_decides y x H'; reflexivity } }
end;

// Commutative properties of ≐

opaque symbol ≐_com x y : π (x ≐ y = opp (y ≐ x)) ≔
begin
  induction
  // case Z0
  { induction { reflexivity } { reflexivity } { reflexivity } }
  // case Zpos
  { assume x;
    induction
     { reflexivity }
     { assume y; simplify; rewrite compare_acc_com; reflexivity }
     { reflexivity } }
  // case Zneg
  { assume x;
    induction
     { reflexivity }
     { reflexivity }
     { assume y; simplify; rewrite compare_acc_com; reflexivity } }
end;

opaque symbol ≐_opp x y : π (— x ≐ — y = opp (x ≐ y)) ≔
begin
  induction
  // case Z0
  { induction { reflexivity } { reflexivity } { reflexivity } }
  // case Zpos
  { assume x;
    induction
     { reflexivity }
     { assume y; simplify; rewrite compare_acc_com; reflexivity }
     { reflexivity } }
  // case Zneg
  { assume x;
    induction
      { reflexivity }
      { reflexivity }
      { assume y; simplify; rewrite opp_idem; reflexivity } }
end;

// General results

opaque symbol simpl_right x a : π ((x + a) - a = x) ≔
begin
  assume x a; simplify; rewrite +_assoc;
  rewrite -_same; rewrite +Z0; reflexivity;
end;

opaque symbol simpl_inv_right x a : π ((x - a) + a = x) ≔
begin
  assume x a; simplify; rewrite +_assoc;
  rewrite .[— a + a] +_com; rewrite -_same; rewrite +Z0; reflexivity;
end;

// ≐ with 0

opaque symbol ≐_double x : π ((double x ≐ Z0) = (x ≐ Z0)) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol ≐_pred_double x :
  π (pred_double x ≐ Z0 = case_Comp (x ≐ Z0) Lt Lt Gt) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol ≐_succ_double x :
  π (succ_double x ≐ Z0 = case_Comp (x ≐ Z0) Gt Lt Gt) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

opaque symbol ≐_pos_sub x y : π ((sub x y ≐ Z0) = compare x y) ≔
begin
  induction
  // case I
  { assume x xrec;
    induction
     { assume y h; simplify; rewrite ≐_double; refine xrec y }
     { assume y h; simplify; rewrite ≐_succ_double; rewrite xrec;
       rewrite compare_Gt; reflexivity }
     { reflexivity } }
  // case O
  { assume x xrec;
    induction
     { assume y h; simplify; rewrite ≐_pred_double; rewrite xrec;
        rewrite compare_Lt; reflexivity }
     { assume y h; simplify; rewrite ≐_double; refine xrec y }
     { reflexivity } }
  // case H
  { induction { reflexivity } { reflexivity } { reflexivity } }
end;

opaque symbol ≐_sub x y : π ((x ≐ y) = (x + — y ≐ Z0)) ≔
begin
  induction
  // case Z0
  { induction { reflexivity } { reflexivity } { reflexivity } }
  // case Zpos
  { assume x;
    induction
     { reflexivity }
     { assume y; simplify; rewrite ≐_pos_sub; reflexivity }
     { reflexivity } }
  // case Zneg
  { assume x;
    induction
     { reflexivity }
     { reflexivity }
     { assume y; simplify; rewrite ≐_pos_sub; rewrite compare_com; reflexivity } }
end;

// Compatibility of comparison with the addition

opaque symbol ≐_compat_add x y z : π ((x ≐ y) = (x + z ≐ y + z)) ≔
begin
  assume x y z;
  rewrite ≐_sub; rewrite .[x in _ = x] ≐_sub;
  rewrite distr_—_+; rewrite .[— y + — z] +_com;
  rewrite +_assoc; rewrite left +_assoc z (— z) (— y);
  rewrite -_same z; reflexivity;
end;

// Directional comparison operators

symbol ≤ x y ≔ ¬ (istrue(isGt(x ≐ y)));
notation ≤ infix 10;

symbol < x y ≔ istrue(isLt(x ≐ y));
notation < infix 10;

symbol ≥ x y ≔ ¬ (x < y);
notation ≥ infix 10;

symbol > x y ≔ ¬ (x ≤ y);
notation > infix 10;

opaque symbol <_≤ x y : π (x < y ⇒ x ≤ y) ≔
begin
  assume x y;
  refine ind_Comp (λ u, istrue(isLt u) ⇒ istrue(isGt u) ⇒ ⊥) _ _ _ (x ≐ y)
   { refine (λ x _, x) }
   { refine (λ _ y, y) }
   { refine (λ x _, x) }
end;

// Compatibility of directional comparison operators

opaque symbol ≤_compat_add x y a : π (x ≤ y ⇒ x + a ≤ y + a) ≔
begin
  assume x y a; simplify;
  assume H; refine fold_⇒ _; rewrite ≐_sub;
  simplify; refine fold_⇒ _; rewrite +_assoc;
  rewrite .[y + a] +_com; rewrite distr_—_+;
  rewrite left +_assoc a (— a) (— y); rewrite -_same;
  rewrite left +_assoc x Z0 (— y); simplify; refine fold_⇒ _;
  rewrite +Z0; rewrite left ≐_sub x y; refine H;
end;

opaque symbol <_compat_add x y a : π (x < y ⇒ x + a < y + a) ≔
begin
  assume x y a; simplify; assume H; rewrite ≐_sub;
  rewrite +_assoc; rewrite .[y + a] +_com;
  rewrite distr_—_+; rewrite left +_assoc a (— a) (— y);
  rewrite -_same; rewrite left +_assoc; rewrite +Z0; 
  rewrite left ≐_sub; refine H;
end;

opaque symbol ≤_compat_≤ x y : π (Z0 ≤ x ⇒ Z0 ≤ y ⇒ Z0 ≤ x + y) ≔
begin
  induction
   { assume y h H; refine H }
   { assume x;
     induction
      { assume h1 h2; refine h1 }
      { assume y h h' i; refine i }
      { assume y h f i; refine f ⊤ᵢ } }
  { assume x y f h i; refine f ⊤ᵢ }
end;

opaque symbol <_compat_≤ x y : π (Z0 < x ⇒ Z0 ≤ y ⇒ Z0 < x + y) ≔
begin
  induction
   { assume y f h; apply ⊥ₑ; refine f }
   { assume x;
     induction
      { assume h1 h2; refine ⊤ᵢ }
      { assume y h h'; refine ⊤ᵢ }
      { simplify; assume y h f; apply ⊥ₑ; refine f ⊤ᵢ } }
  { assume x; assume y f h; apply ⊥ₑ; refine f }
end;

// Reflexivity

opaque symbol ≤_refl x : π (x ≤ x) ≔
begin
  assume x; refine ≤_compat_add Z0 Z0 x _; refine (λ x, x);
end;

// Antisymmetry

opaque symbol ≤_antisym x y : π (x ≤ y ⇒ y ≤ x ⇒ x = y) ≔
begin
  assume x y;
  have e : π (¬ (istrue(isGt (x ≐ y))) ⇒ ¬ (istrue(isGt (y ≐ x))) ⇒ x = y)
  { rewrite ≐_com } ;
  refine ind_Comp (λ c, (y ≐ x) = c ⇒ ¬ (istrue(isGt (opp c))) ⇒ ¬ (istrue(isGt c)) ⇒ x = y) _ _ _ (y ≐ x) _
   { assume H h1 h2; symmetry; refine ≐_decides y x H }
   { assume h1 f h2; apply ⊥ₑ; refine f ⊤ᵢ }
   { assume h1 h2 f; apply ⊥ₑ; refine f ⊤ᵢ }
   { reflexivity; refine e }
end;

// Transitivity theorems

opaque symbol ≤_trans x y z : π (x ≤ y ⇒ y ≤ z ⇒ x ≤ z) ≔
begin
   assume x y z lxy lyz;
   have H : π (Z0 ≤ (z + — y) + (y + — x))
   { refine ≤_compat_≤ (z - y) (y - x) _ _
      { rewrite left -_same y; refine ≤_compat_add y z (— y) _; refine lyz }
      { rewrite left -_same x; refine ≤_compat_add x y (— x) _; refine lxy } } ;
   generalize H; refine fold_⇒ _;
   rewrite +_assoc; rewrite left +_assoc (— y) y (— x);
   rewrite .[— y + y] +_com; rewrite -_same;
   refine (λ p : π ((Z0 ≤ (z + — x)) ⇒ (x ≤ z)), p) _;
   rewrite left .[in x ≤ z] simpl_inv_right z x;
   refine ≤_compat_add Z0 (z - x) x;
end;

opaque symbol <_trans_1 x y z : π (x < y ⇒ y ≤ z ⇒ x < z) ≔
begin
  assume x y z lxy lyz;
  have H : π (Z0 < (z + — y) + (y + — x))
   { rewrite +_com; apply <_compat_≤ (y - x) (z - y)
      { rewrite left -_same x; refine <_compat_add x y (— x) _; refine lxy }
      { rewrite left -_same y; refine ≤_compat_add y z (— y) _; refine lyz } } ;
  generalize H; refine fold_⇒ _;
  rewrite +_assoc; rewrite left +_assoc (— y) y (— x);
  rewrite .[— y + y] +_com; rewrite -_same;
  rewrite left .[in x < z] simpl_inv_right z x;
  refine <_compat_add Z0 (z - x) x;
end;

opaque symbol <_trans_2 x y z : π (x ≤ y ⇒ y < z ⇒ x < z) ≔
begin
  assume x y z lxy lyz;
  have H : π (Z0 < (z + — y) + (y + — x))
  { apply <_compat_≤ (z - y) (y - x)
     { rewrite left -_same y; refine <_compat_add y z (— y) _; refine lyz }
     { rewrite left -_same x; refine ≤_compat_add x y (— x) _; refine lxy } };
  generalize H; refine fold_⇒ _;
  rewrite +_assoc; rewrite left +_assoc (— y) y (— x);
  rewrite .[— y + y] +_com; rewrite -_same;
  rewrite left .[in x < z] simpl_inv_right z x;
  refine <_compat_add Z0 (z - x) x;
end;

// Multiplication

symbol * : ℤ → ℤ → ℤ;
notation * infix right 22;

rule Z0      * _       ↪ Z0
with _       * Z0       ↪ Z0
with Zpos $x * Zpos $y ↪ Zpos (mul $x $y)
with Zpos $x * Zneg $y ↪ Zneg (mul $x $y)
with Zneg $x * Zpos $y ↪ Zneg (mul $x $y)
with Zneg $x * Zneg $y ↪ Zpos (mul $x $y);

// shortcuts

symbol _1 ≔ Zpos _1;
symbol _2 ≔ Zpos _2;
symbol _3 ≔ Zpos _3;
symbol _4 ≔ Zpos _4;
symbol _5 ≔ Zpos _5;
symbol _6 ≔ Zpos _6;
symbol _7 ≔ Zpos _7;
symbol _8 ≔ Zpos _8;
symbol _9 ≔ Zpos _9;
symbol _10 ≔ Zpos _10;

// enable printing of integers in decimal notation

builtin "int_zero" ≔ Z0;
builtin "int_positive" ≔ Zpos;
builtin "int_negative" ≔ Zneg;

// enable parsing of integers in decimal notation

builtin "0" ≔ Z0;
builtin "1" ≔ _1;
builtin "2" ≔ _2;
builtin "3" ≔ _3;
builtin "4" ≔ _4;
builtin "5" ≔ _5;
builtin "6" ≔ _6;
builtin "7" ≔ _7;
builtin "8" ≔ _8;
builtin "9" ≔ _9;
builtin "10" ≔ _10;

builtin "+" ≔ +;
builtin "*" ≔ *;
builtin "-" ≔ —;
