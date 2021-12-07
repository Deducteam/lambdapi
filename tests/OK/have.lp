// test tactic have

symbol A:TYPE;
symbol B:TYPE;
symbol b:B;
symbol h:B → A;

opaque symbol lem:A ≔
begin
  have x:B {apply b};
  apply h;
  apply x
end;
