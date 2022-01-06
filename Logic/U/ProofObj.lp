require open Logic.U.Prop Logic.U.Set;

constant symbol π : Π p, (Prf p → Set) → Set;

rule El (π $p $f) ↪ Π h, El ($f h);
