symbol T:TYPE
symbol a:T
symbol f:(T→T)→T
rule f (λx,$F[x]) ↪ a
assert λx:T,f(λy,x) ≡ λ x:T, a
assert f (λ x, x) ≡ a
