symbol const B : TYPE
symbol const tt : B
symbol const ff : B

symbol neg  : B ⇒ B
symbol conj : B ⇒ B ⇒ B
symbol disj : B ⇒ B ⇒ B

set prefix 5 "¬" ≔ neg
set infix right 6 "∧" ≔ conj
set infix right 5 "∨" ≔ disj

assert tt ∨ ff ∧ ¬ tt ∨ ff ≡ tt ∨ (ff ∧ (¬ tt)) ∨ ff

assert λ p, ¬ (¬ p) ≡ λ p, ¬ ¬ p

assert λ (p:B⇒B) (x:B), ¬ (p x) ≡ λ (p:B⇒B) (x:B), ¬ p x
