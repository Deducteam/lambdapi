symbol N : TYPE;
symbol z : N;

symbol add : N → N → N;
set infix 5 "+" ≔ add;
assert ⊢ z + z + z : N;
