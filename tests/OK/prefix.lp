constant symbol B : TYPE;

symbol conj : B → B → B;
symbol disj : B → B → B;
symbol neg  : B → B;

set infix right 5 "d" ≔ disj;
set infix right 6 "c" ≔ conj;

set prefix 7 "n" ≔ neg;

assert λ x y z t, x d n y c z d t ≡ λx y z t, x d (((n y) c z) d t);

assert λ p, n n p ≡ λ p, n (n p);

assert λ p x, n p x ≡ λ p x, n (p x);
