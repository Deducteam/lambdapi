symbol Prop : TYPE;
symbol prf  : Prop → TYPE;

symbol False     : Prop;
symbol False_elim: Π (A : Prop), prf False → prf A;

symbol ∧         : Prop → Prop → Prop;
notation ∧ infix right 18;
symbol and_intro : Π (A B:Prop), prf A → prf B → prf (A ∧ B);
symbol and_elim1 : Π (A B:Prop), prf (A ∧ B) → prf A;
symbol and_elim2 : Π (A B:Prop), prf (A ∧ B) → prf B;

symbol ↝         : Prop → Prop → Prop;
notation ↝ infix right 14;
symbol imp_elim  : Π (A B:Prop), prf (A ↝  B) → prf A → prf B;
symbol imp_intro : Π (A B:Prop), (prf A → prf B) → prf (A ↝  B);

symbol ∨         : Prop → Prop → Prop;
notation ∨ infix right 16;
symbol or_elim   : Π (A B C:Prop), prf (A ∨ B) → prf (A ↝  C) → prf (B ↝  C) → prf C;
symbol or_intro1 : Π (A B:Prop), prf A → prf (A ∨ B);
symbol or_intro2 : Π (A B:Prop), prf B → prf (A ∨ B);

symbol ¬       : Prop → Prop ≔  λ (P:Prop), P ↝  False;
notation ¬ prefix 20;

symbol to_verify : Π a b,
  (
  Π (x1 : Prop),
  Π (x2 : Prop),
  Π (x3 : Prop),
  Π (x4 : Prop),
  Π (x5 : Prop),
  Π (x6 : Prop),
  Π (x7 : Prop),
  Π (x8 : Prop),
  Π (x9 : Prop),
  Π (y1 : Prop),
  Π (y2 : Prop),
  Π (y3 : Prop),
  Π (y4 : Prop),
  Π (y5 : Prop),
  Π (y6 : Prop),
  Π (y7 : Prop),
  Π (y8 : Prop),
  Π (y9 : Prop),
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  prf (a) →
  prf False) →
  (
  Π (x1 : Prop),
  Π (x2 : Prop),
  Π (x3 : Prop),
  Π (x4 : Prop),
  Π (x5 : Prop),
  Π (x6 : Prop),
  Π (x7 : Prop),
  Π (x8 : Prop),
  Π (x9 : Prop),
  Π (y1 : Prop),
  Π (y2 : Prop),
  Π (y3 : Prop),
  Π (y4 : Prop),
  Π (y5 : Prop),
  Π (y6 : Prop),
  Π (y7 : Prop),
  Π (y8 : Prop),
  Π (y9 : Prop),
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  (Π z1 z2 z3, prf (z1 ∧ z2 ∧ z3 ↝ (z1 ∧ z2) ∧ z3)) →
  prf (a ∧ b) →
  prf False)
≔  λ a b s
     x1 x2 x3 x4 x5 x6 x7 x8 x9
     y1 y2 y3 y4 y5 y6 y7 y8 y9
     H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11
     HG,
   s
   x1 x2 x3 x4 x5 x6 x7 x8 x9
   y1 y2 y3 y4 y5 y6 y7 y8 y9
   H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11
   (and_elim1 a b HG);
