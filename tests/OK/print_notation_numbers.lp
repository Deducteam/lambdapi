symbol N:TYPE;
symbol z:N;
symbol s:N → N;

builtin "nat_zero" ≔ z;
builtin "nat_succ" ≔ s;

compute s(s z);

symbol P:TYPE;
symbol H:P;
symbol O:P → P;
symbol I:P → P;

builtin "pos_one" ≔ H;
builtin "pos_double" ≔ O;
builtin "pos_succ_double" ≔ I;

compute I(O(I H));

symbol double:N → N;
rule double z ↪ z
with double (s $x) ↪ s(s(double $x));

symbol val:P → N;
rule val H ↪ s z
with val (O $x) ↪ double(val $x)
with val (I $x) ↪ s(double(val $x));

compute val(I(O(I H)));

symbol Z:TYPE;
symbol Z0:Z;
symbol Zpos:P → Z;
symbol Zneg:P → Z;

builtin "int_zero" ≔ Z0;
builtin "int_positive" ≔ Zpos;
builtin "int_negative" ≔ Zneg;

compute Zneg(I(O(I H)));
