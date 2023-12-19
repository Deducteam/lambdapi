symbol Prop: TYPE;
symbol π: Prop → TYPE;
symbol Set: TYPE;
constant symbol τ: Set → TYPE;
builtin "T" ≔ τ;
builtin "P" ≔ π;

symbol = [a:Set] : τ a → τ a → Prop;

notation = infix 10;

constant symbol eq_refl [a:Set] (x:τ a) : π (x = x);
constant symbol ind_eq [a:Set] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

symbol set: Set;
symbol cset [T]: (τ T → Prop) → τ set;

symbol T: Set;
symbol P: τ T → Prop;
symbol U: τ set;
symbol Q: τ set → Prop;
symbol th: π (cset (λ x, P x) = U) → π (Q U) → π (Q (cset (λ x, P x))) ≔
begin
  assume h1 h2;
  rewrite h1;
  apply h2;
end;
