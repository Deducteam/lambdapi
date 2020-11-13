constant symbol U : TYPE;

constant symbol u : U;

constant symbol f : (U → U) → TYPE;

symbol G : U → TYPE;

constant symbol H : U → TYPE;

rule G $v ↪ Π (a : H $v), f (λ _, u);
