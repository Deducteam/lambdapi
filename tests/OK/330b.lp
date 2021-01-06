constant symbol Term : TYPE;
constant symbol Prop : TYPE;
symbol prf : Prop → TYPE;
symbol prop_and : Prop → Prop → Prop;
rule prf (prop_and $A $B) ↪ Π C, (prf $A →  prf $B →  prf C) → prf C;

symbol and_elim_1 : Π A B, prf (prop_and A B) → prf A
≔  λ A B h, h A (λ a _, a);
