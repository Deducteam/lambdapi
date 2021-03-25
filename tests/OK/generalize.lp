// test tactic generalize

symbol A:TYPE;
symbol B:A → TYPE;
symbol C:Π x, B x → TYPE;
symbol D:Π x, Π y, C x y → TYPE;
symbol h x y z : D x y z;

opaque symbol lem x y z: D x y z ≔
begin
assume x y z;
generalize y;
assume y z;
apply h x y z;
end;
