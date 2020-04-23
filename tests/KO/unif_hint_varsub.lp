symbol T: TYPE
symbol C: T → T
symbol D: T → T
symbol a: T

// Considering P ≡ Q ↪ &x1 ≡ H1, ..., &xn ≡ Hn,
// we must have {&x1, ..., &xn} ⊆ FV(P) ∪ FV(Q)
set unif_rule C $x ≡ D $y ↪ $z ≡ D a
// here, $z is not in the pattern
