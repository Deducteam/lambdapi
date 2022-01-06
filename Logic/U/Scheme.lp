require open Logic.U.Set;

constant symbol Scheme : TYPE;

symbol Els : Scheme → TYPE;

constant symbol ↑ : Set → Scheme;

rule Els (↑ $a) ↪ El $a;

constant symbol ∀ˢ : (Set → Scheme) → Scheme;

rule Els (∀ˢ $s) ↪ Π a, Els ($s a);
