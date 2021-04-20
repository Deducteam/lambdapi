// Coercions with requisites
constant symbol Set: TYPE;
injective symbol El : Set → TYPE;
constant symbol σ: Set → Set → Set;
constant symbol cons (a: Set) (b: Set): El a → El b → El (σ a b);
constant symbol car (a b: Set): El (σ a b) → El a;
constant symbol cdr (a b: Set): El (σ a b) → El b;
constant symbol int : Set;
constant symbol nat : Set;
constant symbol z : El nat;
constant symbol nat2int : El nat → El int;

coercion "nat2int" nat2int : El nat → El int on 1;

// Coerces tuples provided that we can coerce its elements
coercion "tup" λ a0 b0 a1 b1 t, cons a1 b1 $c[car a0 b0 t] $d[cdr a0 b0 t]
       : Π (a0 b0 a1 b1: Set) (_: El (σ a0 b0)), El (σ a1 b1)
               on 5
with c : El a0 → El a1
with d : El b0 → El b1;

assert ⊢ car int int (cons nat nat z z)
       ≡ car int int (cons int int
                           (nat2int (car nat nat (cons nat nat z z)))
                           (nat2int (cdr nat nat (cons nat nat z z))));
