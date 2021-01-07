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

symbol id : Π {A : Type}, eta (A > A) ≔ λ A x, x;

constant symbol zero : eta i;
constant symbol succ : eta (i > i);

// works
type id zero;
type @id (i > i) succ;
type id succ;

symbol true : eta o ≔ all (λ p, p --> p);
symbol trueI : eps true ≔ λ P p, p;
symbol imp_refl : Π {P : eta o}, eps (P --> P) ≔ λ P prf, prf;
symbol true_imp_true : eps (true --> true) ≔ @imp_refl true;

// works
type @imp_refl true trueI;
type @imp_refl (true --> true) true_imp_true;

// does not work
type imp_refl trueI;
type imp_refl true_imp_true;
