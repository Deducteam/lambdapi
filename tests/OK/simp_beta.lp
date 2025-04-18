symbol A:TYPE;
symbol a:A;
symbol P:A → TYPE;
symbol id (x:A) ≔ x;
opaque symbol l:P(id a) ≔
begin
  simplify id; simplify rule off;
abort;
