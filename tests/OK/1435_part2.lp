require open tests.OK.Nat;

opaque symbol plus_z_r (x:ℕ) : π (x + 0 = x) ≔
begin
  induction
  { reflexivity }
  { assume x' h; simplify; rewrite h; reflexivity }
end;
