require open Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.Nat;

opaque symbol zero_eq_zero : π (0 = 0) ≔
begin
  reflexivity;
end;

opaque symbol eq_sym_nat : Π (x y : ℕ), π (x = y) → π (y = x) ≔
begin
  assume x y h;
  symmetry;
  apply h;
end;
