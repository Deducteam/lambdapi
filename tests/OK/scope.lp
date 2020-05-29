symbol A:TYPE
symbol f:A→A

rule f $x ↪ $x
rule f $x[] ↪ $x
rule f $x ↪ $x[]
rule f $x[] ↪ $x[]

symbol g:(A→A)→A
symbol a:A

rule g (λx,$M) ↪ a

assert g (λx,x) ≡ a

symbol h:(A→A)→A

rule h (λx,$M[]) ↪ a

assertnot h (λx,x) ≡ a
assert h (λ_,a) ≡ a
