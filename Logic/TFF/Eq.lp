// polymorphic Leibniz equality

require open Logic.TFF.Set Logic.TFF.Prop;

constant symbol = [a] : τ a → τ a → Prop;

notation = infix 10;

constant symbol eq_refl [a] (x:τ a) : π (x = x);
constant symbol ind_eq [a] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

// inequality

symbol ≠ [a] (x y : τ a) ≔ ¬ (x = y); // \neq

notation ≠ infix 1;

// symmetry

opaque symbol eq_sym [a] (x y:τ a) : π (x = y ⇒ y = x) ≔
begin
  assume a x y xy; symmetry; apply xy
end;

// monotony wrt function application

opaque symbol feq [a b] (f:τ a → τ b) [x y:τ a] : π(x = y ⇒ f x = f y) ≔
begin
  assume a b f x y xy; apply ind_eq xy (λ z, f z = f y); reflexivity
end;
