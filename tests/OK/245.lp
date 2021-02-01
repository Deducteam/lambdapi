// Improve unification for injective symbols
constant symbol Type : TYPE;
injective symbol eta : Type → TYPE;

// function type
constant symbol Ar : Type → Type → Type;
set infix right 6 ">" ≔ Ar;

rule eta ($a > $b) ↪ eta $a → eta $b;

constant symbol i : Type;
constant symbol o : Type;

injective symbol eps : eta o → TYPE;

constant symbol imp : eta (o > o > o);

rule eps (imp $a $b) ↪ eps $a → eps $b;

set infix right 6 "-->" ≔ imp;

constant symbol all : Π {A : Type}, eta ((A > o) > o);
rule eps (@all $a $b) ↪ Π (x : eta $a), eps ($b x);

// Leibniz equality
symbol eq :
  Π {A : Type}, eta (A > A > o) ≔
  λ A x y, all (λ p , p x 
  --> p y);
set infix right 7 "=" ≔ eq;

// reflexivity of equality
symbol eq_refl :
  Π {A : Type}, eps (@all A (λ x, x = x)) ≔
  λ A x q H, H;

// symmetry of equality
symbol eq_sym :
  Π {A : Type} (x y : eta A),
  eps (x = y --> y = x) ≔
  λ A x y H, H (λ y, y = x) (eq_refl x);
