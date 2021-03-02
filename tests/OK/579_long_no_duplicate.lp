// Encoding taken from OK test firstOrder.dk

constant symbol Prop : TYPE;
symbol prf  : Prop → TYPE;

symbol False     : Prop;
symbol False_elim: Π (A : Prop), prf False → prf A;

symbol ∧         : Prop → Prop → Prop;
set notation ∧ infix right 18;
symbol and_intro : Π (A B:Prop), prf A → prf B → prf (A ∧ B);
symbol and_elim1 : Π (A B:Prop), prf (A ∧ B) → prf A;
symbol and_elim2 : Π (A B:Prop), prf (A ∧ B) → prf B;

symbol ↝         : Prop → Prop → Prop;
set notation ↝ infix right 14;
symbol imp_elim  : Π (A B:Prop), prf (A ↝  B) → prf A → prf B;
symbol imp_intro : Π (A B:Prop), (prf A → prf B) → prf (A ↝  B);

symbol ∨         : Prop → Prop → Prop;
set notation ∨ infix right 16;
symbol or_elim   : Π (A B C:Prop), prf (A ∨ B) → prf (A ↝  C) → prf (B ↝  C) → prf C;
symbol or_intro1 : Π (A B:Prop), prf A → prf (A ∨ B);
symbol or_intro2 : Π (A B:Prop), prf B → prf (A ∨ B);

symbol ¬       : Prop → Prop ≔  λ (P:Prop), P ↝  False;
set notation ¬ prefix 20;


symbol long_to_verify : Π a : Prop, Π b1: Prop, Π b2: Prop, Π b3: Prop, Π b4: Prop, Π b5: Prop, Π b6: Prop, Π b7: Prop, Π b8: Prop, Π b9: Prop, Π b10: Prop, Π b11: Prop, Π b12: Prop, Π b13: Prop, Π b14: Prop, Π b15: Prop, Π b16: Prop, Π b17: Prop, Π b18: Prop, Π b19: Prop, Π b20: Prop,
      (prf b1 →
      prf b2 →
      prf b3 →
      prf b4 →
      prf b5 →
      prf b6 →
      prf b7 →
      prf b8 →
      prf b9 →
      prf b10 →
      prf b11 →
      prf b12 →
      prf b13 →
      prf b14 →
      prf b15 →
      prf b16 →
      prf b17 →
      prf b18 →
      prf b19 →
      prf b20 →
      prf a →
      prf False) →

      (prf b1 →
      prf b2 →
      prf b3 →
      prf b4 →
      prf b5 →
      prf b6 →
      prf b7 →
      prf b8 →
      prf b9 →
      prf b10 →
      prf b11 →
      prf b12 →
      prf b13 →
      prf b14 →
      prf b15 →
      prf b16 →
      prf b17 →
      prf b18 →
      prf b19 →
      prf b20 →
      prf (¬ a) →
      prf False) →

      prf (a ∨ ¬ a) →
      prf b1 →
      prf b2 →
      prf b3 →
      prf b4 →
      prf b5 →
      prf b6 →
      prf b7 →
      prf b8 →
      prf b9 →
      prf b10 →
      prf b11 →
      prf b12 →
      prf b13 →
      prf b14 →
      prf b15 →
      prf b16 →
      prf b17 →
      prf b18 →
      prf b19 →
      prf b20 →
      prf False
≔  λ a b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 s1 s2 H h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9,
   or_elim a (¬ a) False H
   (imp_intro a False (s1 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9))
   (imp_intro (¬ a) False (s2 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9));
