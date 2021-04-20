// Coercions with dependent types: range of the coercion may depend on the
// coerced term.
constant symbol Set : TYPE;
injective symbol El : Set → TYPE;

constant symbol nat : Set;
constant symbol z : El nat;
constant symbol s : El nat → El nat;

constant symbol list : Set → Set;
constant symbol nil (t: Set) : El (list t);
constant symbol cons {t: Set} : El t → El (list t) → El (list t);
symbol length {t: Set}: El (list t) → El nat;
rule length (nil _) ↪ z
with length (cons _ $l) ↪ s (length $l);

constant symbol vec : El nat → Set → Set;
constant symbol vnil (t : Set) : El (vec z t);
constant symbol vcons {t: Set} {n: El nat} :
  El t → El (vec n t) → El (vec (s n) t);

constant symbol lv (l: El (list nat)): El (vec (length l) nat);

constant symbol f_v {t: Set} {n: El nat}: El (vec n t) → El nat;

coercion "list2vec" lv : Π l : El (list nat), El (vec (length l) nat) on 1;
// The range "El (vec (length l) nat)" depends on term "l" that is coerced.

assert ⊢ f_v (cons z (nil nat)) ≡ f_v (lv (cons z (nil nat)));
