symbol U : TYPE;
symbol f : U → TYPE;
symbol trivial : Π A, f A → f A ≔
begin
  solve;
  assume a;
  assume fa;
  apply fa;
end;
