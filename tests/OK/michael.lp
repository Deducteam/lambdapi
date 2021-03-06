constant symbol Type : TYPE;
injective symbol eta : Type → TYPE;

// function type
constant symbol > : Type → Type → Type;
notation > infix right 6;
rule eta ($a > $b) ↪ eta $a → eta $b;

constant symbol i : Type;
constant symbol o : Type;

symbol eps : eta o → TYPE;

constant symbol --> : eta (o > o > o);
notation --> infix right 6;
rule eps ($a --> $b) ↪ eps $a → eps $b;

constant symbol all : Π {A : Type}, eta ((A > o) > o);
rule eps (@all $a $b) ↪ Π (x : eta $a), eps ($b x);

symbol false : eta o ≔ all (λ p, p);

symbol ~ : eta (o > o) ≔ λ p, p --> false;
notation ~ prefix 40;

// these expressions typecheck
type λ p, ~ p;
type λ p, ~ (~ p);
type λ p x, ~ (p x);

// these expressions also typecheck.
type λ p, ~ ~ p;
type λ p x, ~ p x;
