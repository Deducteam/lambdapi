// natural numbers
constant symbol N : TYPE;
constant symbol z : N;
constant symbol s : N → N;

// three parameters function
constant symbol f : N → N → N → N;
assert n m (o:N) ⊢ f n m o ≡ f n m o;
assert n (m:N) ⊢ f n m : N → N;
