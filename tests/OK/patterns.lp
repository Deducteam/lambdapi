// Rewrite rule patterns
symbol E: TYPE;
symbol e: E;
symbol e': E;
symbol Bool: TYPE;
symbol true: Bool;
symbol false: Bool;

symbol id : E → E;
// The pattern ‘$x’ filters any term making ‘id’ the identity on ‘E’
rule id $x ↪ $x;
assert ⊢ λ x, id x ≡ λ x, x;

symbol succ: E → E;
symbol pred: E → E;
// A pattern can contain (possibly applied) function symbols, as the pattern
// ‘pred $e’ here, or ‘pred (succ e)’.
rule succ (pred $e) ↪ $e;
assert ⊢ succ (pred e) ≡ e;
assert ⊢ succ (pred (succ e)) ≡ succ e;

symbol ListE: TYPE;
symbol cons: E → ListE → ListE;
symbol nil: ListE;
symbol map: (E → E) → ListE → ListE;
// A pattern can filter functions as well, such as the pattern ‘$f’ which
// filters functions from ‘E’ to ‘E’.
rule map $f (cons $e $l) ↪ cons ($f $e) (map $f $l);
// The wildcard ‘_’ is always the most general pattern, it filters any term (it
// is an unnamed pattern).
rule map _ nil ↪ nil;
assert ⊢ map id (cons e (cons e nil)) ≡ cons e (cons e nil);
// Another example
symbol diff: (E → E) → E → E;
symbol fprod: (E → E) → (E → E) → E → E;
symbol o: (E → E) → (E → E) → E → E;
// ‘$f’ and ‘$g’ both filter functions
rule diff (o $f $g) ↪ fprod (diff $f) (o (diff $g) $f);

symbol mem: E → ListE → Bool;
// Terms filtered by patterns with the same name must be convertible
rule mem $x (cons $x _) ↪ true;
assert ⊢ mem e (cons e nil) ≡ true;
assertnot ⊢ mem e' (cons e nil) ≡ true;

// Abstractions can be matched, as well as bound variables
rule diff (λ x, x) ↪ λ _, succ e;

// Since application is matched, the previous rule can be written
rule diff (λ x, x) _ ↪ succ e;

symbol cos: E → E;    symbol sin: E → E;
// Terms filtered may contain bound variables if the allowed variables are
// indicated inside brackets as in ‘$v.[x]’, which can contain variable ‘x’.
rule diff (λ x, sin $v.[x]) ↪ fprod (diff (λ x, $v.[x])) cos;

symbol bin: E → E → E;
symbol diff1: (E → E → E) → E → E → E;
// A pattern variable with an environment filters terms that, among the bound
// variables in the scope of the pattern variable, contain at most the ones in
// the environment.
rule diff1 (λ x, λ y, $v.[x]) ↪ λ _, diff (λ x, $v.[x]);
assertnot ⊢ diff1 (λ x y, bin x y) ≡ λ _ _, e;
assert ⊢ diff1 (λ x _, x) ≡ λ _, λ _, succ e;
// this rule can be written more simply as
rule diff1 (λ x _, _) ↪ λ _ _, e;
assertnot ⊢ diff1 (λ x y, bin x y) ≡ λ _ _, e;

symbol scope: (E → E) → E;
rule scope (λ _, $p.[]) ↪ $p.[];
// The environment of a pattern variable only concerns variables in its
// scope at declaration time
assert ⊢ λ x, scope (λ _, x) ≡ λ x, x;
// Here the ‘x’ variable is not introduced by the abstraction matched in the
// rule on ‘scope’, so it may appear in the term that matches ‘$p.[〉’.

symbol f: ((E → E) → E → E) → E;
// Application of bound variables to patterns are authorised
rule f (λ x _, x $p.[]) ↪ $p.[];
assert ⊢ f (λ x _, x e) ≡ e;
