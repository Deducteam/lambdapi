symbol Prop : TYPE;

symbol P : Prop → TYPE;

symbol ∀ : (Prop → Prop) → Prop;
notation ∀ quantifier;

symbol ⇒ : Prop → Prop → Prop;
notation ⇒ infix right 14;

symbol False : Prop ≔ `∀ C, C;

symbol true : TYPE ≔
  P (False ⇒ `∀ C, C);
