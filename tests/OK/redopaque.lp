symbol A: TYPE;
symbol P: A → TYPE;
symbol foo (a: A): A;
redopaque symbol bar (a: A) (_: P a) ≔ foo a;

compute λ (x: A) (h: P x) , bar x h; // Should be printed identically

constant symbol p1 (a: A): P a;
constant symbol p2 (a: A): P a;
assert (a: A) ⊢ bar a (p1 a) ≡ bar a (p2 a);
