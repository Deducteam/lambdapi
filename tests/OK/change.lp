symbol A : TYPE;
symbol B ≔ A;
symbol b:B;

symbol l:A ≔
begin
  change B;
  refine b;
end;
