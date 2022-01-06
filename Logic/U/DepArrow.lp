require open Logic.U.Set;

constant symbol ⤳ᵈ : Π a, (El a → Set) → Set; notation ⤳ᵈ infix right 10;
rule El ($a ⤳ᵈ $b) ↪ Π x : El $a, El ($b x);
