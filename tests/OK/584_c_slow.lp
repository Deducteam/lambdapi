// Encoding taken from OK test firstOrder.dk

constant symbol Prop : TYPE;
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

symbol to_verify :
  (Π (a : Prop), (λ a,
   Π (b1 : Prop), (λ b1,
   Π (b2 : Prop), (λ b2,
   Π (b3 : Prop), (λ b3,
   Π (b4 : Prop), (λ b4,
   Π (b5 : Prop), (λ b5,
   Π (b6 : Prop), (λ b6,
   Π (b7 : Prop), (λ b7,
   Π (b8 : Prop), (λ b8,
   Π (b9 : Prop), (λ b9,
   Π (b10 : Prop), (λ b10,
   Π (b11 : Prop), (λ b11,
   Π (b12 : Prop), (λ b12,
   (prf a →
   prf False)) b12) b11) b10) b9) b8) b7) b6) b5) b4) b3) b2) b1) a) →
  (Π (a : Prop), (λ a,
   Π (b1 : Prop), (λ b1,
   Π (b2 : Prop), (λ b2,
   Π (b3 : Prop), (λ b3,
   Π (b4 : Prop), (λ b4,
   Π (b5 : Prop), (λ b5,
   Π (b6 : Prop), (λ b6,
   Π (b7 : Prop), (λ b7,
   Π (b8 : Prop), (λ b8,
   Π (b9 : Prop), (λ b9,
   Π (b10 : Prop), (λ b10,
   Π (b11 : Prop), (λ b11,
   Π (b12 : Prop), (λ b12,
   (prf (¬ a) →
   prf False)) b12) b11) b10) b9) b8) b7) b6) b5) b4) b3) b2) b1) a) →
  (Π (a : Prop), (λ a,
   Π (b1 : Prop), (λ b1,
   Π (b2 : Prop), (λ b2,
   Π (b3 : Prop), (λ b3,
   Π (b4 : Prop), (λ b4,
   Π (b5 : Prop), (λ b5,
   Π (b6 : Prop), (λ b6,
   Π (b7 : Prop), (λ b7,
   Π (b8 : Prop), (λ b8,
   Π (b9 : Prop), (λ b9,
   Π (b10 : Prop), (λ b10,
   Π (b11 : Prop), (λ b11,
   Π (b12 : Prop), (λ b12,
   (prf (a ∨ ¬ a) →
   prf False)) b12) b11) b10) b9) b8) b7) b6) b5) b4) b3) b2) b1) a)
≔  λ s1 s2 a b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 H,
   or_elim a (¬ a) False H
   (imp_intro a False (λ H, s1 a b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 H))
   (imp_intro (¬ a) False (λ H, s2 a b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 H));
