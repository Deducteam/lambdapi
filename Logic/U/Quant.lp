require open Logic.U.Prop Logic.U.Set;

constant symbol ∀ [a : Set] : (El a → Prop) → Prop; notation ∀ quantifier;

rule Prf (∀ $p) ↪ Π x, Prf ($p x);

constant symbol ∃ [a : Set] : (El a → Prop) → Prop; notation ∃ quantifier;

rule Prf (∃ $p) ↪ Π r, (Π x, Prf ($p x) → Prf r) → Prf r;
