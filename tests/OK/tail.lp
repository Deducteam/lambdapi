constant symbol N:TYPE;
constant symbol o : N;
constant symbol s : N → N;

constant symbol A:TYPE;

constant symbol V:N → TYPE;
constant symbol nil:V o;
constant symbol cons:A → Π n, V n → V(s n);

symbol tail:Π n, V(s n) → V n;

//debug +sui
rule tail _ (cons _ _ $v) ↪ $v;
