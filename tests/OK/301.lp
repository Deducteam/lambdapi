constant symbol U : TYPE;
constant symbol u : U;
symbol Ux : U → TYPE;
rule Ux _ ↪ U;
constant symbol hx : Π (x : U), (Ux x → U) → U;
symbol g : U → U;
rule g $i ↪ hx $i (λ _, u);
