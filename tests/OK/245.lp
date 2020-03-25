constant symbol Type : TYPE
injective symbol eta : Type ⇒ TYPE

// function type
constant symbol Ar : Type ⇒ Type ⇒ Type
set infix right 6 ">" ≔ Ar
rule eta (&a > &b) → eta &a ⇒ eta &b

constant symbol i : Type
constant symbol o : Type

injective symbol eps : eta o ⇒ TYPE

constant symbol imp : eta (o > o > o)
rule eps (imp &a &b) → eps &a ⇒ eps &b
set infix right 6 "-->" ≔ imp

constant symbol all : ∀ {A : Type}, eta ((A > o) > o)
rule eps (@all &a &b) → ∀ (x : eta &a), eps (&b x)

// Leibniz equality
definition eq :
  ∀ {A : Type}, eta (A > A > o) ≔
  λ A x y, all (λ p, p x --> p y)
set infix right 7 "=" ≔ eq

// reflexivity of equality
definition eq_refl :
  ∀ {A : Type}, eps (@all A (λ x, x = x)) ≔
  λ A x q H, H

// symmetry of equality
//set flag "print_domains" on
//set flag "print_implicits" on
//set debug +iu
definition eq_sym :
  ∀ {A : Type} (x y : eta A),
  eps (x = y --> y = x) ≔
  λ A x y H, H (λ y, y = x) (eq_refl x)
