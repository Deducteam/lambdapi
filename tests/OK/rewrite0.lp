// Type of data type codes and their interpretation as types.

constant symbol U : TYPE;

injective symbol T : U → TYPE;

constant symbol pi [a] : (T a → U) → U;

rule T (pi $f) ↪ Π x, T ($f x);

// Data type of booleans.

constant symbol bool : U;

symbol B ≔ T bool;

constant symbol true  : B;
constant symbol false : B;

// Data type of natural numbers.

constant symbol nat  : U;

symbol N ≔ T nat;

constant symbol z : N;
constant symbol s : N → N;

// Addition on natural numbers.

symbol + : N → N → N;

notation + infix left 3;

rule z + $x ↪ $x
with s $x + $y ↪ s ($x + $y);

// Multiplication on natural numbers.

symbol * : N → N → N;

notation * infix left 4;

rule z * _  ↪ z
with s $x * $y ↪ $y + $x * $y;

// Type of propositions and their interpretation as types.

constant symbol Prop : TYPE;

symbol P : Prop → TYPE;

constant symbol all [a] : (T a → Prop) → Prop;

rule P (all $f) ↪ Π x, P ($f x);

// Induction principle on N.

symbol nat_ind p : P(p z) → (Π n, P(p n) → P(p (s n))) → Π n, P(p n);

rule nat_ind _  $u _  z      ↪ $u
with nat_ind $p $u $v (s $n) ↪ $v $n (nat_ind $p $u $v $n);

// Boolean equality on N.

symbol beq : N → N → B;

rule beq z      z      ↪ true
with beq (s $x) (s $y) ↪ beq $x $y
with beq z      (s _ ) ↪ false
with beq (s _ ) z      ↪ false;

// Leibniz equality.

constant symbol = [a] : T a → T a → Prop;

notation = infix 0.1;

constant symbol refl a (x:T a) : P (x = x);

constant symbol eqind a (x y:T a) : P (x = y) → Π p, P (p y) → P (p x);
// FIXME Try to infer the type of p.

// Setting up builtins for rewrite.

builtin "P"     ≔ P;
builtin "T"     ≔ T;
builtin "eq"    ≔ =;
builtin "eqind" ≔ eqind;
builtin "refl"  ≔ refl;

// [Π n m, n + S m = S (n+m)]
opaque symbol add_succ_r n m : P (n + s m = s (n + m))
≔ begin
  assume n m;
  refine nat_ind (λ n, n + s m = s (n + m)) _ _ n
  { // Case z;
  simplify;
  reflexivity }
  { // Case s;
  simplify;
  assume pn ih;
  rewrite ih;
  reflexivity }
end;

opaque symbol test0 x y z : P ((x + s y) + z = (s (x + y)) + z)
≔ begin
  assume x y z;
  rewrite add_succ_r;
  refine refl nat ((s (x + y)) + z)
end;

opaque symbol test1 a (x y : T a) : P(x = y) → P(y = x)
≔ begin
  assume a x y xy;
  rewrite left xy;
  reflexivity
end;

opaque symbol test2 x y : P (x + s(s y) = s(s(x + y))) ≔
begin
  assume x y; repeat rewrite add_succ_r; reflexivity
end;
