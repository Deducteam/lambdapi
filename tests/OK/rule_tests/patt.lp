symbol A:TYPE
symbol f:A→A

// all these rules are equivalent
rule f $x ↪ $x
rule f $x[] ↪ $x
rule f $x ↪ $x[]
rule f $x[] ↪ $x[]

symbol a:A

symbol g:(A→A)→A
rule g (λx,$M[x]) ↪ a
  // Warning: Pattern variable [$M[x]] can be replaced by a wildcard [_].
assert g (λx,x) ≡ a

symbol g2:(A→A)→A
rule g2 (λx,_) ↪ a // equivalent to g2 (λx,$M[x]) ↪ a
assert g2 (λx,x) ≡ a

symbol h:(A→A)→A
rule h (λx,$M[]) ↪ a
  // Warning: Pattern variable [$M] does not need to be named.
  // Warning: Variable [x] could be replaced by [_].
assertnot h (λx,x) ≡ a
assert h (λ_,a) ≡ a

//symbol h2:(A→A)→A
//rule h2 (λx,$M) ↪ a // equivalent to h2 (λx,$M[]) ↪ a
  // Error: Missing square brackets under binder.
//assertnot h2 (λx,x) ≡ a
//assert h2 (λ_,a) ≡ a

symbol h3:(A→A)→A
rule h3 (λ_,_) ↪ a // equivalent to h3 (λx,$M[]) ↪ a
assertnot h3 (λx,x) ≡ a
assert h3 (λ_,a) ≡ a
