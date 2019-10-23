symbol const Type : TYPE
symbol injective eta : Type ⇒ TYPE

// function type
symbol const Ar : Type ⇒ Type ⇒ Type
set infix right 6 ">" ≔ Ar
rule eta (&a > &b) → eta &a ⇒ eta &b

symbol const i : Type
symbol const o : Type

symbol eps : eta o ⇒ TYPE

symbol const imp : eta (o > o > o)
rule eps (imp &a &b) → eps &a ⇒ eps &b
set infix right 6 "-->" ≔ imp

symbol const all : ∀ {A : Type}, eta ((A > o) > o)
rule eps (@all &a &b) → ∀ (x : eta &a), eps (&b x)

definition false : eta o ≔ all (λ p, p)

definition not : eta (o > o) ≔ λ p, p --> false
set prefix 40 "~" ≔ not

// these expressions typecheck
type λ p, ~ p
type λ p, ~ (~ p)
type λ p x, ~ (p x)

// these expressions also typecheck.
type λ p, ~ ~ p
type λ p x, ~ p x
