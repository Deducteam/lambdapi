// binary integers

// following Rocq stdlib
require open tests.OK.Pos;

inductive ℤ : TYPE ≔ // \BbbZ
| Z0 : ℤ
| Zpos : ℙ → ℤ
| Zneg : ℙ → ℤ;

// set code for ℤ

constant symbol int : Set;

rule τ int ↪ ℤ;

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

// Sign

symbol sign : ℤ → ℤ;

rule sign Z0       ↪ Zpos H
with sign (Zpos _) ↪ Zpos H
with sign (Zneg _) ↪ Zneg H;

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

// Compatibility of equality with the addition

opaque symbol =_compat_add x y c : π (x = y) → π (x + c = y + c) ≔
begin
  assume x y c h; rewrite h; reflexivity
end;

opaque symbol =_sub a b : π (a - b = Z0 ⇒ a = b) ≔
begin
  assume a b h;
  have g : π ((a - b) + b = b)
  { simplify; refine =_compat_add (a - b) Z0 b h };
  have g2 : π (a + (b - b) = b)
  { simplify; rewrite +_com b (— b); rewrite left +_assoc; refine g };
  rewrite left +Z0 a;
  rewrite left -_same b;
  refine g2
end;

// Multiplication

symbol * : ℤ → ℤ → ℤ; notation * infix right 22;

rule Z0      * _       ↪ Z0
with _       * Z0       ↪ Z0
with Zpos $x * Zpos $y ↪ Zpos (mul $x $y)
with Zpos $x * Zneg $y ↪ Zneg (mul $x $y)
with Zneg $x * Zpos $y ↪ Zneg (mul $x $y)
with Zneg $x * Zneg $y ↪ Zpos (mul $x $y);

opaque symbol *_com x y : π (x * y = y * x) ≔
begin
  induction
  // case Z0
  { induction { reflexivity } { reflexivity } { reflexivity } }
  // case Zpos
  { assume x;
    induction
     { reflexivity }
     { assume y; simplify; rewrite mul_com; reflexivity }
     { assume y; simplify; rewrite mul_com; reflexivity } }
  // case Zneg
  { assume x;
    induction
     { reflexivity }
     { assume y; simplify; rewrite mul_com; reflexivity }
     { assume y; simplify; rewrite mul_com; reflexivity } }
end;

opaque symbol *_assoc x y z : π ((x * y) * z = x * (y * z)) ≔
begin
  induction
  // case Z0
  { reflexivity }
  // case Zpos
  { assume x;
    induction
     { reflexivity }
     { assume y;
       induction
         { reflexivity }
         { assume z; simplify; rewrite mul_assoc; reflexivity }
         { assume z; simplify; rewrite mul_assoc; reflexivity } }
     { assume y;
       induction
         { reflexivity }
         { assume z; simplify; rewrite mul_assoc; reflexivity }
         { assume z; simplify; rewrite mul_assoc; reflexivity } } }
  // case Zneg
  { assume x;
    induction
     { reflexivity }
     { assume y;
       induction
         { reflexivity }
         { assume z; simplify; rewrite mul_assoc; reflexivity }
         { assume z; simplify; rewrite mul_assoc; reflexivity } }
     { assume y;
       induction
         { reflexivity }
         { assume z; simplify; rewrite mul_assoc; reflexivity }
         { assume z; simplify; rewrite mul_assoc; reflexivity } } }
end;

opaque symbol *_neutral x : π (x * Zpos H = x) ≔
begin
  induction
  { reflexivity }
  { assume p; simplify; rewrite mul_H_right; reflexivity }
  { assume p; simplify; rewrite mul_H_right; reflexivity }
end;

opaque symbol *Z0 x : π (x * Z0 = Z0) ≔
begin
  induction { reflexivity } { reflexivity } { reflexivity }
end;

symbol neg_mul_l a b : π (— (a * b) = (— a) * b) ≔
begin
  induction
  {reflexivity}
  { assume a; induction { reflexivity } { reflexivity } { reflexivity } }
  { assume a; induction { reflexivity } { reflexivity } { reflexivity } }
end;

symbol neg_mul_r a b : π (— (a * b) = a * — b) ≔
begin
  induction
  {reflexivity}
  { assume a; induction { reflexivity } { reflexivity } { reflexivity } }
  { assume a; induction { reflexivity } { reflexivity } { reflexivity } }
end;

opaque symbol *_Zpos_succ (a : ℙ) (s : ℤ) : π (Zpos (succ a) * s = Zpos a * s + s) ≔
begin
  assume a;
  induction
  { reflexivity }
  { assume b; simplify; rewrite mul_succ a b; reflexivity }
  { assume b; simplify; rewrite mul_succ a b; reflexivity }
end;

opaque symbol sub_add_sub (p q r s : ℙ) :
  π (sub p q + sub r s = sub (add p r) (add q s)) ≔
begin
  assume p q r s;
  have e : π (sub p q + (Zpos r + Zneg s) = sub (add p r) (add q s))
  { rewrite left +_assoc (sub p q) (Zpos r) (Zneg s);
    rewrite sub_add_Zpos p q r; rewrite sub_add_Zneg (add p r) q s;
    reflexivity };
  refine e
end;

opaque symbol mul_distr_sub_pos_l (a x y : ℙ) :
  π (Zpos a * sub x y = sub (mul a x) (mul a y)) ≔
begin
  assume a x y;
  refine ind_ℙeano (λ a, Zpos a * sub x y = sub (mul a x) (mul a y)) _ _ a
  { simplify; rewrite *_com (Zpos H) (sub x y); refine *_neutral (sub x y) }
  { assume b IH;
    rewrite *_Zpos_succ b (sub x y); rewrite IH;
    rewrite sub_add_sub (mul b x) (mul b y) x y;
    rewrite left mul_succ b x; rewrite left mul_succ b y; reflexivity }
end;

opaque symbol mul_distr_sub_neg_l (a x y : ℙ) :
  π (Zneg a * sub x y = sub (mul a y) (mul a x)) ≔
begin
  assume a x y;
  have e : π ((— Zpos a) * sub x y = sub (mul a y) (mul a x))
  { rewrite left neg_mul_l (Zpos a) (sub x y);
    rewrite mul_distr_sub_pos_l a x y; refine sub_opp (mul a x) (mul a y) };
  refine e
end;

opaque symbol *_distr_l (z x y : ℤ) : π (z * (x + y) = z * x + z * y) ≔
begin
  induction
  { reflexivity }
  { assume z;
    induction
    { reflexivity }
    { assume x;
      induction
      { reflexivity }
      { assume y; simplify; rewrite mul_distr_l; reflexivity }
      { assume y; simplify; rewrite mul_distr_sub_pos_l; reflexivity } }
    { assume x;
      induction
      { reflexivity }
      { assume y; simplify; rewrite mul_distr_sub_pos_l; reflexivity }
      { assume y; simplify; rewrite mul_distr_l; reflexivity } } }
  { assume z;
    induction
    { reflexivity }
    { assume x;
      induction
      { reflexivity }
      { assume y; simplify; rewrite mul_distr_l; reflexivity }
      { assume y; simplify; rewrite mul_distr_sub_neg_l; reflexivity } }
    { assume x;
      induction
      { reflexivity }
      { assume y; simplify; rewrite mul_distr_sub_neg_l; reflexivity }
      { assume y; simplify; rewrite mul_distr_l; reflexivity } } }
end;

opaque symbol *_distr_r (x y z : ℤ) : π ((x + y) * z = x * z + y * z) ≔
begin
  assume x y z;
  rewrite *_com (x + y) z; rewrite *_com x z; rewrite *_com y z;
  refine *_distr_l z x y
end;

opaque symbol distr_—_*_l a b : π (— (a * b) = (— a) * b) ≔
begin
  induction
  { reflexivity }
  { assume a; induction { reflexivity } { reflexivity } { reflexivity } }
  { assume a; induction { reflexivity } { reflexivity } { reflexivity } }
end;

opaque symbol distr_—_*_r a b : π (— (a * b) = a * — b) ≔
begin
  induction
  { reflexivity }
  { assume a; induction { reflexivity } { reflexivity } { reflexivity } }
  { assume a; induction { reflexivity } { reflexivity } { reflexivity } }
end;

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

// Exponentiation

symbol power_pos (x : ℤ) (p : ℙ) : ℤ;

rule power_pos $x H       ↪ $x
with power_pos $x (O $p)  ↪ let r ≔ power_pos $x $p in r * r
with power_pos $x (I $p)  ↪ let r ≔ power_pos $x $p in $x * r * r;

symbol ^ : ℤ → ℤ → ℤ; notation ^ infix 3;

rule _  ^ Z0        ↪ Zpos H
with $x ^ (Zpos $p) ↪ power_pos $x $p
with _  ^ (Zneg _)  ↪ Z0;

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

opaque symbol ≐_mul_Zpos w r : π ((w * Zpos r ≐ Z0) = (w ≐ Z0)) ≔
begin
  induction
   { reflexivity }
   { reflexivity }
   { reflexivity }
end;

// ℤ has no zero divisor

opaque symbol *=Z0 x y : π (x * y = Z0) → π (x = Z0 ∨ y = Z0) ≔
begin
  induction
  // case Z0
  { assume y h; apply ∨ᵢ₁; reflexivity }
  // case Zpos
  { assume a;
    induction
     { assume h; apply ∨ᵢ₂; reflexivity }
     { assume b h; apply ⊥ₑ (Zpos≠Z0 (mul a b) h) }
     { assume b h; apply ⊥ₑ (Zneg≠Z0 (mul a b) h) } }
  // case Zneg
  { assume a;
    induction
     { assume h; apply ∨ᵢ₂; reflexivity }
     { assume b h; apply ⊥ₑ (Zneg≠Z0 (mul a b) h) }
     { assume b h; apply ⊥ₑ (Zpos≠Z0 (mul a b) h) } }
end;

opaque symbol ≐_refl x : π (x ≐ x = Eq) ≔
begin
  induction
  { reflexivity }
  { induction
     { assume x H; refine H }
     { assume x H; refine H }
     { reflexivity } }
  { induction
     { assume x H; refine H }
     { assume x H; refine H }
     { reflexivity } }
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

opaque symbol ≐_compat_mul x y r : π ((x ≐ y) = (x * Zpos r ≐ y * Zpos r)) ≔
begin
  assume x y r;
  rewrite ≐_sub x y;
  rewrite ≐_sub (x * Zpos r) (y * Zpos r);
  rewrite distr_—_*_l y (Zpos r);
  rewrite left *_distr_r x (— y) (Zpos r);
  rewrite ≐_mul_Zpos (x + — y) r;
  reflexivity
end;

// Regularity of multiplication

opaque symbol *_reg_r x y k : π (k ≠ Z0 ⇒ x * k = y * k ⇒ x = y) ≔
begin
  assume x y;
  induction
  // case Z0
  { assume h0 h; apply ⊥ₑ; refine h0 (eq_refl Z0) }
  // case Zpos
  { assume r h0 h;
    refine ≐_decides x y _;
    rewrite ≐_compat_mul x y r;
    rewrite h;
    refine ≐_refl (y * Zpos r) }
  // case Zneg
  { assume r h0 h;
    have ex : π (x * Zpos r = — (x * Zneg r))
    { symmetry; refine distr_—_*_r x (Zneg r) };
    have ey : π (y * Zpos r = — (y * Zneg r))
    { symmetry; refine distr_—_*_r y (Zneg r) };
    have h2 : π (x * Zpos r = y * Zpos r)
    { rewrite ex; rewrite ey; rewrite h; reflexivity };
    refine ≐_decides x y _;
    rewrite ≐_compat_mul x y r;
    rewrite h2;
    refine ≐_refl (y * Zpos r) }
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

opaque symbol <_¬_≤ x y : π (x < y ⇒ ¬ (y ≤ x)) ≔
begin
  assume x y;
  simplify;
  have e : π (istrue (isLt (x ≐ y)) ⇒ ¬ ¬ (istrue (isGt (y ≐ x))))
  { rewrite ≐_com y x };
  refine ind_Comp (λ c, istrue (isLt c) ⇒ ¬ (¬ (istrue (isGt (opp c))))) _ _ _ (x ≐ y)
  { assume Hbot Hbotbot; refine Hbot }
  { assume H H2; refine H2 H }
  { assume Hbot Hbotbot; refine Hbot };
  assume H1; refine (e H1);
end;

opaque symbol <_¬_≥ x y : π (x < y ⇒ ¬ (x ≥ y)) ≔
begin
  assume x y;
  assume xLty neg_xLty;
  refine neg_xLty xLty
end;

opaque symbol >_¬_≤ x y : π (x > y ⇒ ¬ (x ≤ y)) ≔
begin
  assume x y; refine (λ x, x);
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

opaque symbol ≤_refl x : π (x ≤ x) ≔
begin
  assume x; refine ≤_compat_add Z0 Z0 x _; refine (λ x, x);
end;

opaque symbol ≥_refl x : π (x ≥ x) ≔
begin
  assume x; simplify; assume H;
  have G : π (istrue (isLt Eq)) { rewrite left ≐_refl x; refine H };
  apply ⊥ₑ G
end;

opaque symbol ≥_¬_< x y : π (x ≥ y ⇒ ¬ (x < y)) ≔
begin
  assume x y; assume H; refine H
end;

opaque symbol <_irrefl x : π (¬ (x < x)) ≔
begin
  assume x;
  simplify <;
  refine fold_⇒ _;
  rewrite ≐_refl;
  refine (λ x, x);
end;

opaque symbol >_irrefl x : π (¬ (x > x)) ≔
begin
  assume x;
  simplify >;
  simplify ≤;
  refine fold_⇒ _;
  rewrite ≐_refl;
  simplify;
  assume contra;
  apply contra;
  refine (λ x, x);
end;

opaque symbol =_≤ x y : π (x = y ⇒ x ≤ y) ≔
begin
  assume x y Heq; rewrite Heq; refine ≤_refl y
end;

opaque symbol =_≥ x y : π (x = y ⇒ x ≥ y) ≔
begin
  assume x y Heq; rewrite Heq; refine ≥_refl y
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

// Relating the directional comparison operators

opaque symbol ≥_≤ x y : π (x ≥ y ⇔ y ≤ x) ≔
begin
  assume x y;
  apply ∧ᵢ
  { have e : π (¬ (istrue (isLt (x ≐ y))) ⇒ ¬ (istrue (isGt (y ≐ x))))
    { rewrite ≐_com y x;
      refine ind_Comp (λ c, ¬ (istrue (isLt c)) ⇒ ¬ (istrue (isGt (opp c)))) _ _ _ (x ≐ y)
      { refine (λ x, x) }
      { assume H1 H2; refine H1 H2 }
      { refine (λ x, x) } };
    refine e }
  { have e : π (¬ (istrue (isGt (y ≐ x))) ⇒ ¬ (istrue (isLt (x ≐ y))))
    { rewrite ≐_com y x;
      refine ind_Comp (λ c, ¬ (istrue (isGt (opp c))) ⇒ ¬ (istrue (isLt c))) _ _ _ (x ≐ y)
      { refine (λ x, x) }
      { assume H1 H2; refine H1 H2 }
      { refine (λ x, x) } };
    refine e };
end;

opaque symbol <_> x y : π (x < y ⇔ y > x) ≔
begin
  assume x y;
  apply ∧ᵢ
  { have e : π (istrue (isLt (x ≐ y)) ⇒ ¬ ¬ istrue (isGt (y ≐ x)))
    { rewrite ≐_com;
      refine ind_Comp (λ c, istrue (isLt (opp c)) ⇒ ¬ (¬ (istrue (isGt c)))) _ _ _ (y ≐ x)
      { assume contra; apply ⊥ₑ contra }
      { assume contra; apply ⊥ₑ contra }
      { assume islt ngt; refine ngt islt } };
    refine e }
  { have e : π (¬ ¬ istrue (isGt (y ≐ x)) ⇒ istrue (isLt (x ≐ y)))
    { rewrite ≐_com;
      refine ind_Comp (λ c, ¬ (¬ (istrue (isGt (opp c)))) ⇒ istrue (isLt c)) _ _ _ (x ≐ y)
      { assume H; refine H (λ x, x) }
      { assume H; apply ⊤ᵢ }
      { assume H; refine H (λ x, x) } };
    refine e }
end;

opaque symbol >_≥ x y : π (x > y ⇒ x ≥ y) ≔
begin
  assume x y;
  refine ind_Comp (λ c, ¬ (¬ (istrue (isGt c))) ⇒ ¬ istrue (isLt c)) _ _ _ (x ≐ y)
  { assume H; refine (λ x, x) }
  { assume H H2; refine H (λ x, x) }
  { assume H; refine (λ x, x) }
end;

opaque symbol ¬_≥_< x y : π (¬ (x ≥ y) ⇒ x < y) ≔
begin
  assume x y;
  simplify;
  have e : π (¬ ¬ (istrue (isLt (x ≐ y))) ⇒ istrue (isLt (x ≐ y)))
  { refine ind_Comp (λ c, ¬ ¬ (istrue (isLt c)) ⇒ istrue (isLt c)) _ _ _ (x ≐ y)
    { assume H; refine H (λ x, x) }
    { assume H; apply ⊤ᵢ }
    { assume H; refine H (λ x, x) } };
  refine e
end;

opaque symbol ¬_≤_> x y : π (¬ (x ≤ y) ⇒ x > y) ≔
begin
  assume x y; refine (λ x, x)
end;

// Interaction of the comparison operators with the opposite

opaque symbol ≤_opp x y : π (x ≥ y ⇔ (— x ≤ — y)) ≔
begin
  assume x y;
  simplify;
  rewrite ≐_opp x y;
  apply ∧ᵢ
  { refine ind_Comp (λ c, (istrue (isLt c) ⇒ ⊥) ⇒ (istrue (isGt (opp c)) ⇒ ⊥)) _ _ _ (x ≐ y)
    { assume H; refine H }
    { assume H1 H2; refine H1 H2 }
    { assume H; refine H } }
  { refine ind_Comp (λ c, (istrue (isGt (opp c)) ⇒ ⊥) ⇒ (istrue (isLt c) ⇒ ⊥)) _ _ _ (x ≐ y)
    { assume H; refine H }
    { assume H1 H2; refine H1 H2 }
    { assume H; refine H } }
end;

opaque symbol <_opp x y : π (x > y ⇔ (— x < — y)) ≔
begin
  assume x y;
  simplify;
  rewrite ≐_opp x y;
  apply ∧ᵢ
  { refine ind_Comp (λ c, ((istrue (isGt c) ⇒ ⊥) ⇒ ⊥) ⇒ istrue (isLt (opp c))) _ _ _ (x ≐ y)
    { assume H; refine H (λ x, x) }
    { assume H; refine H (λ x, x) }
    { assume H; apply ⊤ᵢ } }
  { refine ind_Comp (λ c, istrue (isLt (opp c)) ⇒ ((istrue (isGt c) ⇒ ⊥) ⇒ ⊥)) _ _ _ (x ≐ y)
    { assume contra H; apply contra }
    { assume contra H; apply contra }
    { assume Hislt Hngt; refine Hngt Hislt } }
end;

// Comparison with the successor

opaque symbol <_add_Zpos x a : π (x < x + Zpos a) ≔
begin
  assume x a;
  have e : π (x + 0 = x) { refine +Z0 x };
  rewrite left .[t in t < _] e;
  rewrite +_com;
  rewrite +_com x (Zpos a);
  refine <_compat_add 0 (Zpos a) x _;
  apply ⊤ᵢ
end;

opaque symbol ≤_¬_≥_succ t s : π (t ≤ s ⇒ ¬ (t ≥ s + Zpos H)) ≔
begin
  assume t s Ht≤s;
  refine <_¬_≥ t (s + Zpos H) _;
  refine <_trans_2 t s (s + Zpos H) Ht≤s _;
  refine <_add_Zpos s H
end;

// Comparison of a difference with 0

opaque symbol ≥_sub t s : π (t ≥ s ⇒ t - s ≥ 0) ≔
begin
  assume t s H;
  refine ∧ₑ₂ (≥_≤ (t - s) 0) _;
  have g : π (s ≤ t) { refine ∧ₑ₁ (≥_≤ t s) H };
  have g2 : π (s + (— s) ≤ t + (— s)) { refine ≤_compat_add s t (— s) g };
  rewrite left -_same s;
  refine g2
end;

opaque symbol sub_≥ t s : π (t - s ≥ 0 ⇒ t ≥ s) ≔
begin
  assume t s H;
  refine ∧ₑ₂ (≥_≤ t s) _;
  have e : π (0 ≤ t - s) { refine (∧ₑ₁ (≥_≤ (t - s) 0)) H };
  have H2 : π (0 + s ≤ (t - s) + s) { refine ≤_compat_add 0 (t - s) s e };
  have H3 : π (0 + s ≤ t) { rewrite left simpl_inv_right t s; refine H2 };
  refine H3
end;

opaque symbol >_sub t s : π (t > s ⇒ t - s > 0) ≔
begin
  assume t s H;
  refine ∧ₑ₁ (<_> 0 (t - s)) _;
  have g : π (s < t) { refine ∧ₑ₂ (<_> s t) H };
  remove H;
  have g2 : π (s + (— s) < t + (— s)) { refine <_compat_add s t (— s) g };
  rewrite left -_same s;
  refine g2
end;

opaque symbol sub_> t s : π (t - s > 0 ⇒ t > s) ≔
begin
  assume t s H;
  refine ∧ₑ₁ (<_> s t) _;
  have e : π (0 < t - s) { refine (∧ₑ₂ (<_> 0 (t - s))) H };
  have H2 : π (0 + s < (t - s) + s) { refine <_compat_add 0 (t - s) s e };
  have H3 : π (0 + s < t) { rewrite left simpl_inv_right t s; refine H2 };
  refine H3
end;

// Compatibility of comparison with the multiplication

opaque symbol <_compat_mul x y r : π (x < y ⇔ x * Zpos r < y * Zpos r) ≔
begin
  assume x y r; simplify; rewrite ≐_compat_mul x y r; refine ⇔_refl
end;

opaque symbol <_compat_mul_pos p : π (Z0 < p) → Π x y, π (x < y ⇔ x * p < y * p) ≔
begin
  induction
   { assume h x y; refine ⊥ₑ h }
   { assume r h x y; refine <_compat_mul x y r }
   { assume r h x y; refine ⊥ₑ h }
end;

opaque symbol ≤_compat_mul x y r : π (x ≤ y ⇔ x * Zpos r ≤ y * Zpos r) ≔
begin
  assume x y r; simplify; rewrite ≐_compat_mul x y r; refine ⇔_refl
end;

opaque symbol >_compat_mul x y r : π (x > y ⇔ x * Zpos r > y * Zpos r) ≔
begin
  assume x y r; simplify; rewrite ≐_compat_mul x y r; refine ⇔_refl
end;

opaque symbol ≥_compat_mul x y r : π (x ≥ y ⇔ x * Zpos r ≥ y * Zpos r) ≔
begin
  assume x y r; simplify; rewrite ≐_compat_mul x y r; refine ⇔_refl
end;

opaque symbol ≐_mul_opp x y z : π ((x * — z ≐ y * — z) = opp (x * z ≐ y * z)) ≔
begin
  assume x y z;
  rewrite left distr_—_*_r x z;
  rewrite left distr_—_*_r y z;
  refine ≐_opp (x * z) (y * z)
end;

opaque symbol ≐_compat_mul_neg z : π (Z0 < z) → Π x y, π ((y ≐ x) = (x * — z ≐ y * — z)) ≔
begin
  induction
   { assume h x y; refine ⊥ₑ h }
   { assume r h x y;
     have e : π ((x * — Zpos r ≐ y * — Zpos r) = opp (x * Zpos r ≐ y * Zpos r))
     { refine ≐_mul_opp x y (Zpos r) };
     rewrite e;
     rewrite left ≐_compat_mul x y r;
     refine ≐_com y x }
   { assume r h x y; refine ⊥ₑ h }
end;

opaque symbol <_compat_mul_neg z : π (Z0 < z) → Π x y, π (x < y ⇔ y * — z < x * — z) ≔
begin
  induction
   { assume h x y; refine ⊥ₑ h }
   { assume r h x y; simplify;
     rewrite ≐_compat_mul_neg (Zpos r) ⊤ᵢ y x; refine ⇔_refl }
   { assume r h x y; refine ⊥ₑ h }
end;

opaque symbol ≤_compat_mul_neg z : π (Z0 < z) → Π x y, π (x ≤ y ⇔ y * — z ≤ x * — z) ≔
begin
  induction
   { assume h x y; refine ⊥ₑ h }
   { assume r h x y; simplify;
     rewrite ≐_compat_mul_neg (Zpos r) ⊤ᵢ y x; refine ⇔_refl }
   { assume r h x y; refine ⊥ₑ h }
end;

opaque symbol *_pos x y : π (0 < x ⇒ 0 < y ⇒ 0 < x * y) ≔
begin
  induction
  { assume y h1 h2; refine ⊥ₑ h1 }
  { assume a;
    induction
     { assume h1 h2; refine ⊥ₑ h2 }
     { assume b h1 h2; refine ⊤ᵢ }
     { assume b h1 h2; refine ⊥ₑ h2 } }
  { assume a y h1 h2; refine ⊥ₑ h1 }
end;
