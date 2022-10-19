require open tests.OK.Prop tests.OK.Set;

constant symbol = [a] : τ a → τ a → Prop;

notation = infix 10;

constant symbol eq_refl [a] (x:τ a) : π (x = x);
constant symbol ind_eq [a] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

symbol ≠ [a] (x y : τ a) ≔ ¬ (x = y); notation ≠ infix 10; // \neq

opaque symbol feq [a b] (f:τ a → τ b) [x x':τ a] : π(x = x') → π(f x = f x') ≔
begin
  assume a b f x x' xx'; rewrite xx'; reflexivity;
end;

opaque symbol feq2 [a b c] (f:τ a → τ b → τ c):
  Π [x x':τ a], π(x = x') → Π [y y':τ b], π(y = y') → π(f x y = f x' y') ≔
begin
  assume a b c f x x' xx' y y' yy'; rewrite xx'; rewrite yy'; reflexivity
end;

opaque symbol eq_sym [a] [x y:τ a] : π(x = y) → π(y = x) ≔
begin
  assume a x y h; symmetry; apply h
end;
