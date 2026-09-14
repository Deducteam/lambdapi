require open tests.OK.Set tests.OK.Prop tests.OK.Eq;
require open tests.OK.String tests.OK.Tactic;

constant symbol T:Set;
constant symbol f: τ T → τ T;

symbol test (a b: τ T) (h: π (a = b)): π (f a = f b) ≔
begin
  assume a b h;
  // f a = f b is seen as p a where p x = (f x = f b)
  eval (#abstract a (f a = f b) (λ p _, #apply (ind_eq [T] [a] [b] h p)));
  reflexivity
end;


