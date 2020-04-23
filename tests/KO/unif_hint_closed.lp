symbol T: TYPE
symbol C: T → T
symbol D: T → T
symbol a: T

// The RHS of unification hints must not depend on the patterns
hint C $x ≡ D _ ↪ $x ≡ D $x
// so here, [D &x] raises an error
