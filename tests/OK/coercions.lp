constant symbol Nat: TYPE;
constant symbol Float: TYPE;
constant symbol round (_: Float): Nat;
coercion #c Float $t Nat ↪ round $t;
constant symbol succ (_: Nat): Nat;
assert (x: Float) ⊢ succ x ≡ succ (round x);

// Coercion with holes
constant symbol List: TYPE;
constant symbol SortedList: TYPE;
constant symbol sortedp (_: List): TYPE;
constant symbol sorted (l: List) (_: sortedp l): SortedList;
coercion #c List $l SortedList ↪ sorted $l _;  
constant symbol min (_: SortedList): Nat;

assert (l: List) ⊢ min l: Nat;
assert (l: List) ⊢ min (sorted l _): Nat;

// Parametric coercions
constant symbol Set: TYPE;
injective symbol El (_: Set): TYPE;
constant symbol nat: Set;
constant symbol float: Set;
symbol round! (_: El float): El nat;
coercion #c (El float) $t (El nat) ↪ round! $t;
constant symbol cell (_ _: Set): Set;
constant symbol cons [a: Set] [b: Set] (x: El a) (y: El b): El (cell a b);
symbol car [a: Set] [b: Set] (_: El (cell a b)): El a;
symbol cdr [a: Set] [b: Set] (_: El (cell a b)): El b;
coercion #c (El (cell $a $b)) $t (El (cell $c $d)) ↪
  cons (#c (El $a) (car $t) (El $c)) (#c (El $b) (cdr $t) (El $d));
assert (x y: El float) ⊢ cons [float] [float] x y: El (cell nat nat);

// Note that it does not work if the implicit arguments are not set:
assertnot (x y: El float) ⊢ cons x y: El (cell nat nat);
// this is because unification constraints are delayed. To pass this
// example, we need to first unify then apply coercions in
// Infer.coerce
