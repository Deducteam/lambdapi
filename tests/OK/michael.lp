constant symbol Type : TYPE;
injective symbol eta : Type → TYPE;

// function type
constant symbol Ar : Type → Type → Type;
set infix right 6 ">" ≔ Ar;
rule eta ($a > $b) ↪ eta $a → eta $b;

constant symbol i : Type;
constant symbol o : Type;

symbol eps : eta o → TYPE;

constant symbol imp : eta (o > o > o);
rule eps (imp $a $b) ↪ eps $a → eps $b;
set infix right 6 "-->" ≔ imp;

constant symbol all : Π {A : Type}, eta ((A > o) > o);
rule eps (@all $a $b) ↪ Π (x : eta $a), eps ($b x);

symbol false : eta o ≔ all (λ p, p);

symbol not : eta (o > o) ≔ λ p, p --> false;
set prefix 40 "~" ≔ not;

// these expressions typecheck
type λ p, ~ p;
type λ p, ~ (~ p);
type λ p x, ~ (p x);

// these expressions also typecheck.
type λ p, ~ ~ p;
type λ p x, ~ p x;
