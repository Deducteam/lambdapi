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

definition id : ∀ {A : Type}, eta (A > A) ≔ λ A x, x

symbol const zero : eta i
symbol const succ : eta (i > i)

// works
type id zero
type @id (i > i) succ
type id succ

definition true : eta o ≔ all (λ p, p --> p)
definition trueI : eps true ≔ λ P p, p
definition imp_refl : ∀ {P : eta o}, eps (P --> P) ≔ λ P prf, prf
definition true_imp_true : eps (true --> true) ≔ @imp_refl true

// works
type @imp_refl true trueI
type @imp_refl (true --> true) true_imp_true

// does not work
type imp_refl trueI
type imp_refl true_imp_true
