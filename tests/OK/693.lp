constant symbol Set: TYPE;

injective symbol τ: Set → TYPE;

builtin "T" ≔ τ;

constant symbol Prop: TYPE;

symbol π: Prop → TYPE;

builtin "P" ≔ π;

constant symbol ⇒: Prop → Prop → Prop; notation ⇒ infix right 10;

rule π ($p ⇒ $q) ↪ π $p → π $q;

constant symbol = {a} : τ a → τ a → Prop; notation = infix 20;

constant symbol eq_refl {a} (x:τ a) : π (x = x);
constant symbol ind_eq {a} {x y:τ a} : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

symbol fold_arrow {p1 p2 : Prop} : π (p1 ⇒ p2) → π p1 → π p2
≔ λ p1_p2 p1, p1_p2 p1;

constant symbol nat: Set;

symbol test_assume (a b : τ nat) f : π (a = b ⇒ f a ⇒ f b) ≔
begin
  assume a b f; assume eab; rewrite eab; assume fb; apply fb;
end;
