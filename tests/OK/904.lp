/* test tactic generalize */
symbol A:TYPE;
symbol B:TYPE;
symbol C:TYPE;
symbol F:A → B → C → TYPE;
opaque symbol lemma (x:A) (y:B) (z:C) : F x y z ≔
begin
  assume x y z; generalize x;
abort;
