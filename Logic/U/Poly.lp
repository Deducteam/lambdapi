require open Logic.U.Prop Logic.U.Set;

constant symbol ∀ᵖ : (Set → Prop) → Prop;

rule Prf (∀ᵖ $p) ↪ Π a, Prf ($p a);
