require open tests.OK.List tests.OK.Prop tests.OK.Eq tests.OK.Set;

opaque symbol rot_size [a] (l:𝕃 a) : π (rot (size l) l = l) ≔
begin
  assume a l; simplify; rewrite take_size; rewrite drop_size; reflexivity
end;
