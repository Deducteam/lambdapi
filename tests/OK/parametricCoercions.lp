constant symbol Set: TYPE;
injective symbol El (_: Set): TYPE;

// Pairs
constant symbol * (_ _: Set): Set;
notation * infix right 3;
constant symbol pair [l: Set] [r: Set] (_: El l) (_: El r): El (l * r);
symbol fst [l: Set] [r: Set] (_: El (l * r)): El l;
symbol snd [l: Set] [r: Set] (_: El (l * r)): El r;
rule fst (pair $x _) ↪ $x;
rule snd (pair _ $y) ↪ $y;

// Parametric coercion
coerce_rule coerce (El ($l1 * $r1)) (El ($l2 * $r2)) $t ↪
  pair (coerce (El $l1) (El $l2) (fst $t))
       (coerce (El $r1) (El $r2) (snd $t));

// Ground types
constant symbol nat: Set;
constant symbol posnat: Set;

constant symbol natOfPosnat (_: El posnat): El nat;
coerce_rule coerce (El posnat) (El nat) $x ↪ natOfPosnat $x;

constant symbol one: El posnat;
// And a typing problem
assert ⊢ one : El nat; // Non parametric
assert ⊢ pair [posnat] [posnat] one one : El (nat * nat);
//!\\ Arguments must be explicit for coercions to work

type pair [nat] [nat] one one;
assert ⊢ pair [nat] [nat] one one
       ≡ pair [nat] [nat] (natOfPosnat one) (natOfPosnat one);
