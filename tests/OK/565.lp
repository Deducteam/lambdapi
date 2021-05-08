// Encoding taken from OK test firstOrder.dk

constant symbol Prop : TYPE;
symbol prf  : Prop → TYPE;

symbol False     : Prop;
symbol False_elim: Π (A : Prop), prf False → prf A;

symbol ∧       : Prop → Prop → Prop;
notation ∧ infix right 18;
symbol and_intro : Π (A B:Prop), prf A → prf B → prf (A ∧ B);
symbol and_elim1 : Π (A B:Prop), prf (A ∧ B) → prf A;
symbol and_elim2 : Π (A B:Prop), prf (A ∧ B) → prf B;

symbol ↝       : Prop → Prop → Prop;
notation ↝ infix right 14;
symbol imp_elim  : Π (A B:Prop), prf (A ↝  B) → prf A → prf B;
symbol imp_intro : Π (A B:Prop), (prf A → prf B) → prf (A ↝  B);

symbol ∨        : Prop → Prop → Prop;
notation ∨ infix right 16;
symbol or_elim   : Π (A B C:Prop), prf (A ∨ B) → prf (A ↝  C) → prf (B ↝  C) → prf C;
symbol or_intro1 : Π (A B:Prop), prf A → prf (A ∨ B);
symbol or_intro2 : Π (A B:Prop), prf B → prf (A ∨ B);

symbol ¬       : Prop → Prop ≔  λ (P:Prop), P ↝  False;
notation ¬ prefix 20;

symbol id : Π A,
    prf ¬ A →
    (prf ¬ A → prf False) →
    prf False
≔  λ A na s, s na;


debug +i;
symbol or_elim_long_to_verify :
   Π (A B: Prop),
   prf ¬ A →
   prf ¬ B →
   prf (A ∨ B) →
   prf False
≔  λ A B a b ab,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   id A a (λ a,
   or_elim A B False ab a b
   ))))))))))))))))))))))
   ;
