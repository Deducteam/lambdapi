symbol const B : TYPE
symbol const tt : B
symbol const ff : B

symbol neg  : B ⇒ B
symbol conj : B ⇒ B ⇒ B
symbol disj : B ⇒ B ⇒ B

set prefix 5 "¬" ≔ neg
set infix right 5 "∧" ≔ conj
set infix right 6 "∨" ≔ disj

type tt ∨ ff ∧ tt ∨ ff

type λ p, ¬ p

type λ p, ¬ (¬ p)
type λ p, ¬ ¬ p

type λ (p : B ⇒ B) (x : B), ¬ (p x)
type λ (p : B ⇒ B) (x : B), ¬ p x

type ¬ ¬ ¬ tt
