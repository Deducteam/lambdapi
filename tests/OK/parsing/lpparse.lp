symbol A : TYPE;
symbol a: A;
symbol f: A → A;

symbol g: Π(x:A), A;

symbol id : A → A ≔ λ(x: A), x;
symbol id2 (x: A) ≔ x;

rule g $x ↪ f $x;

// A one line comment

/* A multiline
comment */

symbol B: TYPE;
symbol b: B;
symbol mob: B → B → A;
notation mob infix left 6;
type b mob b;
assert ⊢ b mob b: A;
