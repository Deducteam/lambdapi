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

symbol S: Set;
symbol a: τ S;
symbol cset [T]: (τ T → Prop) → τ S;

symbol th: π (a = a) ≔
begin
  flag "print_implicits" on;
  flag "print_domains" on;
  set E ≔ @cset S (λ x, @= S x x);
  have h:π (E = `cset x:τ S, x = x) { reflexivity };
  reflexivity
end;
