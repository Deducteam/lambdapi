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

symbol ¬       : Prop → Prop ≔  λ (P:Prop), P ↝ False;
notation ¬ prefix 20;

symbol ax : Π A B, prf A → prf (¬ A ↝ B)
≔ λ A B a, imp_intro (¬ A) B (λ na, False_elim B (imp_elim A False na a));

symbol to_verify :
     Π p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
     p21 p22 p23 p24 p25 p26 p,
     prf p1 →
     prf (¬ p1 ∨ p2) →
     prf (¬ p2 ∨ p3) →
     prf (¬ p3 ∨ p4) →
     prf (¬ p4 ∨ p5) →
     prf (¬ p5 ∨ p6) →
     prf (¬ p6 ∨ p7) →
     prf (¬ p7 ∨ p8) →
     prf (¬ p8 ∨ p9) →
     prf (¬ p9 ∨ p10) →
     prf (¬ p10 ∨ p11) →
     prf (¬ p11 ∨ p12) →
     prf (¬ p12 ∨ p13) →
     prf (¬ p13 ∨ p14) →
     prf (¬ p14 ∨ p15) →
     prf (¬ p15 ∨ p16) →
     prf (¬ p16 ∨ p17) →
     prf (¬ p17 ∨ p18) →
     prf (¬ p18 ∨ p19) →
     prf (¬ p19 ∨ p20) →
     prf (¬ p20 ∨ p21) →
     prf (¬ p21 ∨ p22) →
     prf (¬ p22 ∨ p23) →
     prf (¬ p23 ∨ p24) →
     prf (¬ p24 ∨ p25) →
     prf (¬ p25 ∨ p26) →
     prf (¬ p26 ∨ p) →
     prf p

≔ λ p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19
    p20 p21 p22 p23 p24 p25 p26 p h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26,

    or_elim (¬ p1) p2 p h1 (ax p1 p h0) (imp_intro p2 p (λ h1,
    or_elim (¬ p2) p3 p h2 (ax p2 p h1) (imp_intro p3 p (λ h2,
    or_elim (¬ p3) p4 p h3 (ax p3 p h2) (imp_intro p4 p (λ h3,
    or_elim (¬ p4) p5 p h4 (ax p4 p h3) (imp_intro p5 p (λ h4,
    or_elim (¬ p5) p6 p h5 (ax p5 p h4) (imp_intro p6 p (λ h5,
    or_elim (¬ p6) p7 p h6 (ax p6 p h5) (imp_intro p7 p (λ h6,
    or_elim (¬ p7) p8 p h7 (ax p7 p h6) (imp_intro p8 p (λ h7,
    or_elim (¬ p8) p9 p h8 (ax p8 p h7) (imp_intro p9 p (λ h8,
    or_elim (¬ p9) p10 p h9 (ax p9 p h8) (imp_intro p10 p (λ h9,
    or_elim (¬ p10) p11 p h10 (ax p10 p h9) (imp_intro p11 p (λ h10,
    or_elim (¬ p11) p12 p h11 (ax p11 p h10) (imp_intro p12 p (λ h11,
    or_elim (¬ p12) p13 p h12 (ax p12 p h11) (imp_intro p13 p (λ h12,
    or_elim (¬ p13) p14 p h13 (ax p13 p h12) (imp_intro p14 p (λ h13,
    or_elim (¬ p14) p15 p h14 (ax p14 p h13) (imp_intro p15 p (λ h14,
    or_elim (¬ p15) p16 p h15 (ax p15 p h14) (imp_intro p16 p (λ h15,
    or_elim (¬ p16) p17 p h16 (ax p16 p h15) (imp_intro p17 p (λ h16,
    or_elim (¬ p17) p18 p h17 (ax p17 p h16) (imp_intro p18 p (λ h17,
    or_elim (¬ p18) p19 p h18 (ax p18 p h17) (imp_intro p19 p (λ h18,
    or_elim (¬ p19) p20 p h19 (ax p19 p h18) (imp_intro p20 p (λ h19,
    or_elim (¬ p20) p21 p h20 (ax p20 p h19) (imp_intro p21 p (λ h20,
    or_elim (¬ p21) p22 p h21 (ax p21 p h20) (imp_intro p22 p (λ h21,
    or_elim (¬ p22) p23 p h22 (ax p22 p h21) (imp_intro p23 p (λ h22,
    or_elim (¬ p23) p24 p h23 (ax p23 p h22) (imp_intro p24 p (λ h23,
    or_elim (¬ p24) p25 p h24 (ax p24 p h23) (imp_intro p25 p (λ h24,
    or_elim (¬ p25) p26 p h25 (ax p25 p h24) (imp_intro p26 p (λ h25,
    or_elim (¬ p26) p p h26 (ax p26 p h25) (imp_intro p p (λ h26,
    h26))))))))))))))))))))))))))))))))))))))))))))))))))));
