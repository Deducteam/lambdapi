require open Logic.U.Set;

constant symbol ⤳ : Set → Set → Set; notation ⤳ infix right 10;
rule El ($x ⤳ $y) ↪ El $x → El $y;
