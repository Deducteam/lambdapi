symbol T: TYPE
symbol C: T → T
symbol D: T → T
symbol a: T

// Non linear rhs
set unif_rule C $x ≡ D _ ↪ $x ≡ a, $x ≡ a
