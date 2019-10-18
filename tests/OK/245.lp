symbol const Type : TYPE
symbol injective eta : Type ⇒ TYPE

// function type
symbol const Ar : Type ⇒ Type ⇒ Type
set infix right 6 ">" ≔ Ar
rule eta (&a > &b) → eta &a ⇒ eta &b

symbol const i : Type
symbol const o : Type

symbol injective eps : eta o ⇒ TYPE

symbol const imp : eta (o > o > o)
rule eps (imp &a &b) → eps &a ⇒ eps &b
set infix right 6 "-->" ≔ imp

symbol const all : ∀ {A : Type}, eta ((A > o) > o)
rule eps (@all &a &b) → ∀ (x : eta &a), eps (&b x)

// Leibniz equality
definition eq : ∀ A, eta (A > A > o) ≔ λ A x y, all (λ p, p x --> p y)

//type λ A x y, all (λ p, p x --> p y)
