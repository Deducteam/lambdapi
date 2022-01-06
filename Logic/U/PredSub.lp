require open Logic.U.Set Logic.U.Prop;

constant symbol psub [a] : (El a → Prop) → Set;

protected symbol pair† [a] [p : El a → Prop] : El a → El (psub p);

symbol pair [a] [p : El a → Prop] x (_ : Prf (p x)) ≔ pair† [a] [p] x;

symbol fst [a] [p : El a → Prop] : El (psub p) → El a;

rule fst (pair† $x) ↪ $x;

constant symbol snd [a] [p : El a → Prop] (r : El (psub p)) : Prf (p (fst r));
