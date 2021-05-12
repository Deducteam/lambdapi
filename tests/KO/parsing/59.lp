symbol A : TYPE;
symbol a : A;
symbol f : (A → A) → A;

rule f (λ x, $y[x,x]) ↪ a;

