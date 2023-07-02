symbol A:TYPE;
symbol B:A → TYPE;
symbol C a:B a → TYPE;

//debug +t;

opaque symbol lemma : A → A ≔
begin
  assume a;
  remove a;
abort;

opaque symbol lemma a (b:B a) (c:C a b) : A ≔
begin
  assume a b c;
  remove c;
  remove a b;
abort;
