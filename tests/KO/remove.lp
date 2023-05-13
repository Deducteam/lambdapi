symbol A:TYPE;
symbol B:A → TYPE;
symbol C a:B a → TYPE;

opaque symbol lemma a (b:B a) (c:C a b) : A ≔
begin
  assume a b c;
  remove a;
abort;
