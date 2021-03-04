// Encoding taken from OK test firstOrder.dk

constant symbol Prop : TYPE;
symbol prf  : Prop → TYPE;

symbol False     : Prop;
symbol False_elim: Π (A : Prop), prf False → prf A;

symbol ∧       : Prop → Prop → Prop;
set notation ∧ infix right 18;
symbol and_intro : Π (A B:Prop), prf A → prf B → prf (A ∧ B);
symbol and_elim1 : Π (A B:Prop), prf (A ∧ B) → prf A;
symbol and_elim2 : Π (A B:Prop), prf (A ∧ B) → prf B;

symbol ↝       : Prop → Prop → Prop;
set notation ↝ infix right 14;
symbol imp_elim  : Π (A B:Prop), prf (A ↝  B) → prf A → prf B;
symbol imp_intro : Π (A B:Prop), (prf A → prf B) → prf (A ↝  B);

symbol ∨        : Prop → Prop → Prop;
set notation ∨ infix right 16;
symbol or_elim   : Π (A B C:Prop), prf (A ∨ B) → prf (A ↝  C) → prf (B ↝  C) → prf C;
symbol or_intro1 : Π (A B:Prop), prf A → prf (A ∨ B);
symbol or_intro2 : Π (A B:Prop), prf B → prf (A ∨ B);

symbol ¬       : Prop → Prop ≔  λ (P:Prop), P ↝  False;
set notation ¬ prefix 20;

symbol long_to_verify : Π a : Prop, Π b: Prop,
      (prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf a →
      prf False) →

      (prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf (¬ a) →
      prf False) →

      prf (a ∨ ¬ a) →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf b →
      prf False
≔  λ a b s1 s2 H h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9,
   or_elim a (¬ a) False H
   (imp_intro a False (s1 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9))
   (imp_intro (¬ a) False (s2 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9));
