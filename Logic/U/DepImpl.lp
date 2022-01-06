require open Logic.U.Prop;

constant symbol ⇒ᵈ : Π p, (Prf p → Prop) → Prop; notation ⇒ᵈ infix right 10;

rule Prf ($a ⇒ᵈ $b) ↪ Π x : Prf $a, Prf ($b x);
