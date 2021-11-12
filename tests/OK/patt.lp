symbol A:TYPE;
symbol f: A → A;

// all these rules are equivalent
rule f $x ↪ $x;
rule f $x 〈 〉 ↪ $x;
rule f $x ↪ $x 〈 〉;
rule f $x 〈 〉 ↪ $x 〈 〉;

symbol a:A;

symbol g:(A → A) → A;
rule g (λ x,$M 〈 x 〉) ↪ a;
  // Warning: Pattern variable [$M 〈 x 〉] can be replaced by a wildcard [_].
assert ⊢ g (λ x,x) ≡ a;

symbol g2:(A → A) → A;
rule g2 (λ x,_) ↪ a; // equivalent to g2 (λ x,$M 〈 x 〉) ↪ a
assert ⊢ g2 (λ x,x) ≡ a;

symbol h:(A → A) → A;
rule h (λ x, $M 〈 〉) ↪ a;
  // Warning: Pattern variable [$M] does not need to be named.
  // Warning: Variable [x] could be replaced by [_].
assertnot ⊢ h (λ x, x) ≡ a;
assert ⊢ h (λ _, a) ≡ a;

//symbol h2:(A → A) → A;
//rule h2 (λ x, $M) ↪ a; // equivalent to h2 (λx,$M 〈 〉) ↪ a
  // Error: Missing square brackets under binder.
//assertnot h2 (λ x, x) ≡ a;
//assert h2 (λ _, a) ≡ a;

symbol h3:(A → A) → A;
rule h3 (λ _, _) ↪ a; // equivalent to h3 (λx,$M 〈 〉) ↪ a
assertnot ⊢ h3 (λ x, x) ≡ a;
assert ⊢ h3 (λ _, a) ≡ a;
